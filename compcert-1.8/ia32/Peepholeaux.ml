(* A Peephole optimizer for use in the Compcert framework *)
open Camlcoq
open Datatypes
open Asm
open List
open PrintAsm

let compose (f : 'b -> 'c) (g : 'a -> 'b) (a : 'a) : 'c = f (g a)

let rec splitAt n xs =
	match n with
	| 0 -> ([],xs)
	| _ -> match xs with
		| []     -> ([],[])
		| (b::bs) -> let (y,z) = splitAt (n-1) bs in (b::y,z)

let rec windowNPeephole n optFunc is =
  match is with
  | [] -> is
  | _  ->
    let (opt,rest) = splitAt n is in
      match optFunc opt with
      | [] -> windowNPeephole n optFunc rest
      | (o::os) -> o :: windowNPeephole n optFunc (append os rest)

let loadStore (is : instruction list) : instruction list =
  match is with
  | Pmov_rm (r1, m1) :: Pmov_mr (m2, r2) :: xs when beq_ireg r1 r2 && beq_addrmode m1 m2 ->
        Pmov_rm (r1, m1) :: Pnop :: xs
  | Pmov_mr (m1, r1) :: Pmov_rm (r2, m2) :: xs when beq_ireg r1 r2 && beq_addrmode m1 m2 ->
	Pmov_mr (m1, r1) :: Pnop :: xs
  | _ -> is

let loadLoad (is : instruction list) : instruction list =
  match is with
  | Pmovd_rf (r1, _) :: Pmov_rr (r2, rs) :: xs when beq_ireg r1 r2 ->
      Pnop :: Pmov_rr (r2,rs) :: xs
  | Pmov_rm (r1, _) :: Pmov_rr (r2, rs) :: xs when beq_ireg r1 r2 ->
      Pnop :: Pmov_rr (r2, rs) :: xs
  | _ -> is

let rec skipReadsDropLoadsTo (rX : ireg) (mX : addrmode) (ts : instruction list) : instruction list =
  let rec op is = 
    match is with
     | Pmov_rm (r1, m1) :: rest when beq_ireg r1 rX && beq_addrmode m1 mX
          ->
	 Pnop :: op rest
     | Pmov_rm (r1, m1) :: rest when negb (beq_ireg r1 rX) ->
	  Pmov_rm (r1, m1) :: op rest
     | Pmov_rm (r1, m1) :: rest when beq_ireg r1 rX && negb (beq_addrmode m1 mX) ->
           is
     | Pmov_mr (_, _) :: rest -> is
     | x::xs -> x::op xs (* This isn't always right, any instruction that
                            stores in a possibly aliased manner should stop us *)
     | []    -> []
   in op ts

let loadSkipLoad (is : instruction list) : instruction list =
  match is with
  | Pmov_rm (r1, m1) :: rest -> Pmov_rm (r1,m1) :: skipReadsDropLoadsTo r1 m1 rest
  | _ -> is

(* All optimizations that use a window of 2 adjacent instructions can go here *)
let window2Opts : (instruction list -> instruction list) list = 
  [loadStore; loadLoad]

let window3Opts : (instruction list -> instruction list) list =
   []

(* Optimizations that can operate on arbitrary window sizes *)
let windowNOpts : (instruction list -> instruction list) list =
   [loadSkipLoad]

(* This is a list of all optimizations, they will be applied once per pass *)
let optimizations : (instruction list -> instruction list) list =
  concat [map (windowNPeephole 2) window2Opts;
          map (windowNPeephole 3) window3Opts;
          map (fun o is -> windowNPeephole (length is) o is) windowNOpts
         ]

(* A single pass applies all our optimizations (in no particular order) once *)
let singlePass : instruction list -> instruction list =
  fold_left compose (fun x -> x) optimizations


let rec allSame g f =
  match (g,f) with
  | ([], [])  -> true
  | ([], _)   -> false
  | (_, [])   -> false
  | (x::xs, y::ys) -> beq_instr x y && allSame xs ys

let rec ml_optimize_loop f n =
  let g = singlePass f in
    if n == 0 || allSame g f then g else ml_optimize_loop g (n-1)

let ml_optimize f =
  let g = ml_optimize_loop f 500 in
         g
