# hacspec language

```
    Items i :=
      | use u; (* import modules *)
      | const x : tau = c; (* constant variables *)
      | type y = tau'; (* type aliases *)
      | array!(y, tau, c); (* fixed-length array declaration *)
      | poly!(y’, y, a); (* fixed-length polynomials *)    
      | field_integers!(y, c, c); (* abstract field integer declaration *)
      | fn f([x: (&)tau,]+) -> tau' { e } (* function *)
      | enum y { [z(tau),]+ } (* enum type *)
      | struct y { [f: tau,]+ } (* struct type *)

    Use path u :=
      | [m::]*m' (* sequence of nested modules*)

    Type tau :=
      | bool | usize
      | u8 | u16 | u32 | u64 | u128 | U8 | U16 | U32 | U64 | U128
      | i8 | i16 | i32 | i64 | i128 | I8 | I16 | I32 | I64 | I128
      | Seq<tau> (* Unknown-length array *)
      | y (* type variable *)
      | ([tau,]+) (* tuples *)

    Statement s :=
      | let (mut) p (: tau) = e (* let binding *)
      | x = e (* mutable variable reassignment *)
      | if e1 { e2 } (else { e3 }) (* if statement | Maybe we want this to be an expression? *)
      | for x in e1..e2 { s } (* for loop *)
      | s1; s2 (* sequencing *)
      | x[e1] = e2 (* array update *)

    Expression e :=
      | l (* literal *) | (u::)x (* variable *)
      | (u::)(y::)f([(&)e]+); (* function call *)
      | e.f([e']+)  (* method call *)
      | ([e]) (* tuple *)
      | e1.n (* tuple member access *)
      | e1..e2 (* range *)
      | e1 op e2 (* arithmetic operations *) | unop e (* unary op *)
      | x[e] (* array indexing *)
      | e1 as e2 (* UNsafe integer casting *)

    Operator op := + | - | * | / | ^ | && | || | & | | | % | >> | << |
       | == | != | <= | >=
    Unary operator unop := ~ | ! | -

    Pattern p :=
      | x
      | ([p,]*) (* tuple destructuring *)
      | _ (* wildcard *)
```

## Print primitive/forbidden functions

Inside `hacspec/`,

```
cargo +nightly build --features="print_attributes"
```

## How to use Creusot - Pearlite with Hacspec

See [creusot](https://github.com/xldenis/creusot) for documentation about pearlite. When used in conjunction with hacspec it is important to only use the hacspec subset in the pearlite annotation, otherwise it will not get through the typechecker. You should still be able to use creusot by
```
cargo creusot
```
in the crate you want to analyze. This might require updating the version in rust-toolchain to match the version used by creusot (this is how creusot finds relevant packages to analyze). To compile hacspec code to pearlite statements in coq run
```
cargo clean
cargo install --path language
cargo build
cargo hacspec -e v -o <output_file_name> -dir <output_dir> <crate_name>
```

To get it working add the following to the Cargo.toml file of the project:
```
[dependencies.creusot-contracts]
git = "https://github.com/xldenis/creusot/"
branch = "master"
package = "creusot-contracts"
```
And the lines 
```
#[cfg(not(feature = "hacspec"))]
extern crate hacspec_lib;

#[cfg(feature = "hacspec")]
use hacspec_attributes::*;

#[cfg(not(feature = "hacspec"))]
extern crate creusot_contracts;
#[cfg(not(feature = "hacspec"))]
pub use creusot_contracts::*;

pub use hacspec_lib::*;
```
to the hacspec file using creusot/pearlite
