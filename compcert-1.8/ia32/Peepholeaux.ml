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

let loadLoad (is : instruction list) : instruction list =
  match is with
  | Pmovd_rf (r1, _) :: Pmov_rr (r2, rs) :: xs when r1 = r2 ->
      Pnop :: Pmov_rr (r2,rs) :: xs
  | Pmovl_rm (r1, _) :: Pmov_rr (r2, rs) :: xs when r1 =r2 ->
      Pnop :: Pmov_rr (r2, rs) :: xs
  | _ -> is

(* currently, this code optimizes a specific pattern we see, but could
   be made more general. The pattern is:

        ...
	movl	%edx, 4(%esp)
	movl	%ebx, 0(%edx)
	movl	%edx, 4(%esp)
        ...

   note that I've manually fixed the above to look like the usual
   intel syntax. the actual output from the optimizer is in at&t
   syntax... just in case it wasn't confusing enough... 

   also note that this particular example is exactly the case where we
   need to make sure the second load to edx is remove, not the first
   one...  *)

let loadSkipLoad (is : instruction list) : instruction list =
  match is with
  | Pmov_rm (r1, m1) :: Pmov_rm (r2, m2) :: Pmov_rm (r3, m3) :: xs
    when r1 = r3 && m1 = m3 &&
      Pmov_rm (r1, m1) :: Pmov_rm (r2, m2) :: Pnop :: xs
   | _ -> is

(* All optimizations that use a window of 2 adjacent instructions can go here *)
let window2Opts : (instruction list -> instruction list) list = 
  [loadStore; loadLoad]

let window3Opts : (instruction list -> instruction list) list =
   [loadSkipLoad]

(* This is a list of all optimizations, they will be applied once per pass *)
let optimizations : (instruction list -> instruction list) list =
  concat [map (windowNPeephole 2) window2Opts;
   map (windowNPeephole 3) window3Opts
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
         print_string "PREOPTIMIZE:\n";
         print_function_debug stdout f;
         print_string "\n";
         print_string "POST:\n";
         print_function_debug stdout g;
         g
