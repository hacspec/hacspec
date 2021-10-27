use hacspec_lib::*;

array!(UserAddress, 32, u8); // U8

#[derive(Clone)]
pub enum AuctionState {
    /// The auction is either
    /// - still accepting bids or
    /// - not accepting bids because it's past the auction end, but nobody has
    ///   finalized the auction yet.
    NotSoldYet,
    /// The auction is over and the item has been sold to the indicated address.
    Sold(UserAddress), // winning account's address
}

unfold_struct! {
    struct SeqMap {
        a : PublicByteSeq,
        b : PublicByteSeq,
    }
}

pub type Amount = u64;
pub type Timestamp = u64;

pub type Itemtyp = Seq<u8>;

unfold_struct! {
    struct State {
        auction_state: AuctionState,
        highest_bid: Amount,
        item: Itemtyp, // Vec<u8>
        expiry: Timestamp,
        bids: SeqMap, // BTreeMap<AccountAddress, Amount>,
    }
}

pub fn fresh_state(itm: Seq<u8>, exp: u64) -> State {
    State(
        AuctionState::NotSoldYet,
        0_u64,
        itm,
        exp,
        SeqMap (PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
    )
}

pub enum MapEntry {
    Entry(u64, SeqMap),
}

fn seq_map_entry(m: SeqMap, sender_address: UserAddress) -> MapEntry {
    let SeqMap (m0, m1) = m;

    let mut res = MapEntry::Entry(
        0_u64,
        SeqMap (
            m0.clone().concat(&sender_address),
            m1.clone().concat(&u64_to_be_bytes(0_u64)),
        ),
    );

    for x in 0..m0.clone().len() / 32 {
        if UserAddress::from_seq(&m0.clone().slice(x * 32, 32)) == sender_address {
            res = MapEntry::Entry(
                u64_from_be_bytes(u64Word::from_seq(&m1.slice(x * 8, 8))),
                SeqMap (m0.clone(), m1.clone()),
            );
        }
    }

    res
}

pub enum MapUpdate {
    Update(u64, SeqMap),
}

fn seq_map_update_entry(m: SeqMap, sender_address: UserAddress, amount: u64) -> MapUpdate {
    let SeqMap (m0, m1) = m;

    let mut res = MapUpdate::Update(
        amount,
        SeqMap (
            m0.concat(&sender_address),
            m1.concat(&u64_to_be_bytes(amount)),
        ),
    );

    for x in 0..m0.clone().len() / 32 {
        if UserAddress::from_seq(&m0.clone().slice(x * 32, 32)) == sender_address {
            res = MapUpdate::Update(
                amount,
                SeqMap (
                    m0.clone().update(x * 32, &sender_address),
                    m1.clone().update(x * 8, &u64_to_be_bytes(amount)),
                ),
            );
        }
    }

    res
}

pub enum BidError {
    ContractSender, // raised if a contract, as opposed to account, tries to bid
    BidTooLow,      /* { bid: Amount, highest_bid: Amount } */
    // raised if bid is lower than highest amount
    BidsOverWaitingForAuctionFinalization, // raised if bid is placed after auction expiry time
    AuctionIsFinalized,                    /* raised if bid is placed after auction has been
                                            * finalized */
}

// pub type UserAddressSet = Option<UserAddress>;
pub enum UserAddressSet {
    UserAddressSome(UserAddress, ()),
    UserAddressNone,
}
pub type Context = (u64, UserAddressSet);
pub type AuctionBidResult = Result<(), BidError>;

pub enum Boolean {
    True,
    False,
}

pub fn auction_bid(ctx: Context, amount: u64, state: State) -> (State, AuctionBidResult) {
    let (slot_time, sender) = ctx;

    let State(st0, st1, st2, st3, st4) = state.clone();

    let (new_state, rese) = match st0 {
        AuctionState::NotSoldYet => match if slot_time <= st3 {
            Boolean::True
        } else {
            Boolean::False
        } {
            Boolean::True => match sender {
                UserAddressSet::UserAddressNone => {
                    (state, AuctionBidResult::Err(BidError::ContractSender))
                }
                UserAddressSet::UserAddressSome(sender_address, _) => {
                    match seq_map_entry(st4.clone(), sender_address) {
                        MapEntry::Entry(bid_to_update, new_map) => match seq_map_update_entry(
                            new_map.clone(),
                            sender_address,
                            bid_to_update + amount,
                        ) {
                            MapUpdate::Update(updated_bid, updated_map) => {
                                match if updated_bid > st1 {
                                    Boolean::True
                                } else {
                                    Boolean::False
                                } {
                                    Boolean::True => (
                                        State(st0, updated_bid, st2, st3, updated_map),
                                        AuctionBidResult::Ok(()),
                                    ),
                                    Boolean::False => (
                                        State(st0, st1, st2, st3, updated_map),
                                        AuctionBidResult::Err(BidError::BidTooLow),
                                    ),
                                }
                            }
                        },
                    }
                }
            },
            Boolean::False => (
                state,
                AuctionBidResult::Err(BidError::BidsOverWaitingForAuctionFinalization),
            ),
        },
        AuctionState::Sold(_) => (state, AuctionBidResult::Err(BidError::AuctionIsFinalized)),
    };

    (
        new_state,
        rese,
    )
}

pub type FinalizeContext = (u64, UserAddress, u64);

/// For errors in which the `finalize` function can result
pub enum FinalizeError {
    BidMapError,
    AuctionStillActive,
    AuctionFinalized,
}

pub enum FinalizeAction {
    Accept,
    SimpleTransfer(UserAddress, u64, PublicByteSeq),
}

pub enum BidRemain {
    None,
    Some(u64, ()),
}

pub type AuctionFinalizeResult = Result<FinalizeAction, FinalizeError>;

pub fn auction_finalize(ctx: FinalizeContext, state: State) -> (State, AuctionFinalizeResult) {
    let State(mut st0, st1, st2, st3, st4) = state.clone();
    let (slot_time, owner, balance) = ctx;

    let (continues, mut return_action) = match st0 {
        AuctionState::NotSoldYet => {
            if slot_time > st3 {
                if balance == 0_u64 {
                    (false, AuctionFinalizeResult::Ok(FinalizeAction::Accept))
                } else {
                    (
                        true,
                        AuctionFinalizeResult::Ok(FinalizeAction::SimpleTransfer(
                            owner,
                            st1,
                            PublicByteSeq::new(0_usize),
                        )),
                    )
                }
            } else {
                (
                    false,
                    AuctionFinalizeResult::Err(FinalizeError::AuctionStillActive),
                )
            }
        }
        AuctionState::Sold(_) => (
            false,
            AuctionFinalizeResult::Err(FinalizeError::AuctionFinalized),
        ),
    };

    let mut remaining_bid = BidRemain::None;

    let SeqMap (m0, m1) = st4.clone();

    if continues {
        // Return bids that are smaller than highest
        // let aucstate = auction_state;
        for x in 0..m0.clone().len() / 32 {
            let amnt = u64_from_be_bytes(u64Word::from_seq(&m1.slice(x * 8, 8)));
            let addr = UserAddress::from_seq(&m0.clone().slice(x * 32, 32));
            if amnt < st1 {
                return_action = match return_action {
                    AuctionFinalizeResult::Ok(a) => match a {
                        FinalizeAction::SimpleTransfer(o, b, a) => {
                            AuctionFinalizeResult::Ok(FinalizeAction::SimpleTransfer(
                                o,
                                b,
                                a.concat(&addr).concat(&u64_to_be_bytes(amnt)),
                            ))
                        }
                        FinalizeAction::Accept => AuctionFinalizeResult::Ok(FinalizeAction::Accept),
                    },
                    AuctionFinalizeResult::Err(e) => AuctionFinalizeResult::Err(e),
                };
            } else {
                if match remaining_bid {
                    BidRemain::None => true,
                    BidRemain::Some(_, _) => false,
                } {
                    st0 = AuctionState::Sold(addr);
                    remaining_bid = BidRemain::Some(amnt, ());
                } else {
                    return_action = AuctionFinalizeResult::Err(FinalizeError::BidMapError);
                }
            }
        }
    };

    if continues {
        // Ensure that the only bidder left in the map is the one with the highest bid
        return_action =
            // match return_action {
            //     AuctionFinalizeResult::Ok (_) =>
                    match remaining_bid {
                        BidRemain::Some(amount, _) =>
                            match if amount == st1 { Boolean::True } else { Boolean::False } {
                                Boolean::True => return_action,
                                Boolean::False => AuctionFinalizeResult::Err(FinalizeError::BidMapError),
                            },
                        BidRemain::None => AuctionFinalizeResult::Err(FinalizeError::BidMapError),
                    }; // ,
                       // AuctionFinalizeResult::Err (e) => AuctionFinalizeResult::Err (e)
                       // };

        // return_action = res;
    };

    (State(st0, st1, st2, st3, st4), return_action) // (auction_state, b, c, expiry, (m1, m2))
}

#[cfg(proof)]
#[test]
/// Test that the smart-contract initialization sets the state correctly
/// (no bids, active state, indicated auction-end time and item name).
pub fn auction_test_init() -> bool {
    let item = PublicByteSeq::new(0_usize);
    let time = 100_u64;

    fresh_state(item.clone(), time)
        == State(
            AuctionState::NotSoldYet,
            0_u64,
            item.clone(),
            time,
            SeqMap (PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
        )
}

#[cfg(proof)]
fn verify_bid(
    state: State,
    account: UserAddress,
    ctx: Context,
    amount: u64,
    highest_bid: u64,
) -> (State, bool) {
    let item = PublicByteSeq::new(0_usize);
    let time = 100_u64;

    let (State(auc_st, hb, its, tm, bm), res) = auction_bid(ctx, amount, state);
    let bm = match seq_map_update_entry(bm.clone(), account, highest_bid) {
        MapUpdate::Update(_, updated_map) => updated_map,
    };

    (
        State(auc_st, hb, its.clone(), tm, bm.clone()),
        State(auc_st, hb, its.clone(), tm, bm.clone())
            == State(
                AuctionState::NotSoldYet,
                highest_bid,
                item.clone(),
                time,
                bm.clone(),
            ),
    )
}

// const AUCTION_END: u64 = 1;

// fn new_account() -> AccountAddress {
//     let account = AccountAddress([0; 32]);
//     ADDRESS_COUNTER.fetch_add(1, Ordering::SeqCst);
//     account
// }

// #[cfg(proof)]
// fn new_account_ctx() -> (UserAddress, Context) {
//     let account = new_account();
//     let ctx = new_ctx(account, account, 1_u64);
//     (account, ctx)
// }

// #[cfg(proof)]
// fn new_ctx(
//     owner: UserAddress,
//     sender: UserAddress,
//     slot_time: u64,
// ) -> Context {
//     // let mut ctx = Context;
//     // ctx.set_sender(Address::Account(sender));
//     // ctx.set_owner(owner);
//     // ctx.set_metadata_slot_time(Timestamp::from_timestamp_millis(slot_time));
//     // ctx
//     (slot_time, sender)
// }

#[cfg(proof)]
#[test]
/// Test a sequence of bids and finalizations:
/// 0. Auction is initialized.
/// 1. Alice successfully bids 0.1 GTU.
/// 2. Alice successfully bids another 0.1 GTU, highest bid becomes 0.2 GTU
/// (the sum of her two bids). 3. Bob successfully bids 0.3 GTU, highest
/// bid becomes 0.3 GTU. 4. Someone tries to finalize the auction before
/// its end time. Attempt fails. 5. Dave successfully finalizes the
/// auction after its end time.    Alice gets her money back, while
/// Carol (the owner of the contract) collects the highest bid amount.
/// 6. Attempts to subsequently bid or finalize fail.
fn test_auction_bid_and_finalize() -> bool {
    let item = PublicByteSeq::new(0_usize);
    let time = 100_u64;

    let amount = 100_u64;
    let winning_amount = 300_u64;
    // let big_amount = 500_u64;

    // initializing auction
    let state = fresh_state(item.clone(), time); // mut

    // 1st bid: account1 bids amount1
    let alice = (UserAddress([
        0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8,
        0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8,
        0_u8, 0_u8,
    ]));
    let alice_ctx = (1_u64, UserAddressSet::UserAddressSome(alice, ()));

    let (state, result_0) =
	verify_bid(state, alice, alice_ctx, amount, amount);

    // // 2nd bid: account1 bids `amount` again
    // // should work even though it's the same amount because account1 simply
    // // increases their bid
    let (state, result_1) =
        verify_bid(state, alice, alice_ctx, amount, amount + amount);

    // // 3rd bid: second account
    let bob = (UserAddress([
        1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8,
        1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8, 1_u8,
        1_u8, 1_u8,
    ]));
    let bob_ctx = (2_u64, UserAddressSet::UserAddressSome(bob, ()));

    let (state, result_2) =
	verify_bid(state, bob, bob_ctx, winning_amount, winning_amount);

    let owner = (UserAddress([
        0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8,
        0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8,
        0_u8, 0_u8,
    ]));

    let sender = owner;
    let balance = 100_u64;
    let ctx4 = (1_u64, owner, balance);

    let (state, finres) = auction_finalize(ctx4, state);

    let result_3 = match finres {
	AuctionFinalizeResult::Err(err) =>
	    match err {
		FinalizeError::AuctionStillActive => true,
		FinalizeError::BidMapError => false,
		FinalizeError::AuctionFinalized => false,
	    },
	AuctionFinalizeResult::Ok(_) => false,
    };

    // // finalizing auction
    // let carol = new_account();
    let carol = (UserAddress([
        2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8,
        2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8, 2_u8,
        2_u8, 2_u8,
    ]));
    let carol_ctx = (2_u64, UserAddressSet::UserAddressSome(carol, ()));

    // // let dave = new_account();
    // let dave = (UserAddress([
    //     3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8,
    //     3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8, 3_u8,
    //     3_u8, 3_u8,
    // ]));
    // let dave_ctx = (3_u64, UserAddressSet::UserAddressSome(dave, ()));

    let ctx5 = (2_u64, carol, winning_amount);

    let (state, finres2) = auction_finalize(ctx5, state);


    
    
    // let actions = finres2.expect("Finalizing auction should work");
    // assert_eq!(
    //     actions,
    //     ActionsTree::simple_transfer(&carol, winning_amount)
    //         .and_then(ActionsTree::simple_transfer(&alice, amount + amount))
    // );
    // assert_eq!(state, make_state (
    //     AuctionState::Sold(bob),
    //     winning_amount,
    //     ITEM.as_bytes().to_vec(),
    //     Timestamp::from_timestamp_millis(AUCTION_END),
    //     bid_map,
    // ));

    // // attempting to finalize auction again should fail
    // let finres3: Result<ActionsTree, _> = auction_finalize(&ctx5, &mut state);
    // expect_error(
    //     finres3,
    //     FinalizeError::AuctionFinalized,
    //     "Finalizing auction a second time should fail",
    // );

    // // attempting to bid again should fail
    // let res4: Result<ActionsTree, _> = auction_bid(&bob_ctx, big_amount, &mut state);
    // expect_error(
    //     res4,
    //     BidError::AuctionFinalized,
    //     "Bidding should fail because the auction is finalized",
    // );

    result_0 && result_1 && result_2 && result_3
}
