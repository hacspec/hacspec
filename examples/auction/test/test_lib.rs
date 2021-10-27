fn test_init_smash_zero () -> bool {
    match piggy_smash((42, 42, 0, piggy_init())) {
	Result::Ok ((ctx, owner, balance)) => balance == 0,
	Result::Err (()) => false,
    }
}
