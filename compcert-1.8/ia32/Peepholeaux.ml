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
  | Pmov_rm (r1, m1) :: Pmov_mr (m2, r2) :: xs when r1 = r2 && m1 = m2 ->
        Pmov_rm (r1, m1) :: Pnop :: xs
  | Pmov_mr (m1, r1) :: Pmov_rm (r2, m2) :: xs when r1 = r2 && m1 = m2 ->
	Pmov_mr (m1, r1) :: Pnop :: xs
  | _ -> is

(* All optimizations that use a window of 2 adjacent instructions can go here *)
let window2Opts : (instruction list -> instruction list) list = 
  [loadStore]

(* This is a list of all optimizations, they will be applied once per pass *)
let optimizations : (instruction list -> instruction list) list =
  concat [map (windowNPeephole 2) window2Opts
         ]

(* A single pass applies all our optimizations (in no particular order) once *)
let singlePass : instruction list -> instruction list =
  fold_left compose (fun x -> x) optimizations


let rec ml_optimize_loop f n =
  let g = singlePass f in
    if n == 0 then g else ml_optimize_loop g (n-1)

let ml_optimize f =
  print_string "Optimizing...\n" ;
  let g = ml_optimize_loop f 500 in
    if g = f then g else ml_optimize g
(*
         print_string "PREOPTIMIZE:\n";
         print_function_debug stdout f;
         print_string "\n";
         print_string "POST:\n";
         print_function_debug stdout g;
         g
*)