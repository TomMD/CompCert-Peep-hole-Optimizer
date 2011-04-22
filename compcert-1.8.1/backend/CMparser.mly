/* *********************************************************************/
/*                                                                     */
/*              The Compcert verified compiler                         */
/*                                                                     */
/*          Xavier Leroy, INRIA Paris-Rocquencourt                     */
/*                                                                     */
/*  Copyright Institut National de Recherche en Informatique et en     */
/*  Automatique.  All rights reserved.  This file is distributed       */
/*  under the terms of the GNU General Public License as published by  */
/*  the Free Software Foundation, either version 2 of the License, or  */
/*  (at your option) any later version.  This file is also distributed */
/*  under the terms of the INRIA Non-Commercial License Agreement.     */
/*                                                                     */
/* *********************************************************************/

%{
open Datatypes
open Camlcoq
open BinPos
open BinInt
open Integers
open AST
open Cminor

(** Naming function calls in expressions *)

type rexpr =
  | Rvar of ident
  | Rconst of constant
  | Runop of unary_operation * rexpr
  | Rbinop of binary_operation * rexpr * rexpr
  | Rload of memory_chunk * rexpr
  | Rcondition of rexpr * rexpr * rexpr
  | Rcall of signature * rexpr * rexpr list

let temp_counter = ref 0

let temporaries = ref []

let mktemp () =
  incr temp_counter;
  let n = Printf.sprintf "__t%d" !temp_counter in
  let id = intern_string n in
  temporaries := id :: !temporaries;
  id

let convert_accu = ref []

let rec convert_rexpr = function
  | Rvar id -> Evar id
  | Rconst c -> Econst c
  | Runop(op, e1) -> Eunop(op, convert_rexpr e1)
  | Rbinop(op, e1, e2) ->
      let c1 = convert_rexpr e1 in
      let c2 = convert_rexpr e2 in
      Ebinop(op, c1, c2)
  | Rload(chunk, e1) -> Eload(chunk, convert_rexpr e1)
  | Rcondition(e1, e2, e3) ->
      let c1 = convert_rexpr e1 in
      let c2 = convert_rexpr e2 in
      let c3 = convert_rexpr e3 in
      Econdition(c1, c2, c3)
  | Rcall(sg, e1, el) ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      let t = mktemp() in
      convert_accu := Scall(Some t, sg, c1, cl) :: !convert_accu;
      Evar t

and convert_rexpr_list = function
  | [] -> []
  | e1 :: el ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      c1 :: cl

let rec prepend_seq stmts last =
  match stmts with
  | [] -> last
  | s1 :: sl -> prepend_seq sl (Sseq(s1, last))

let mkeval e =
  convert_accu := [];
  match e with
  | Rcall(sg, e1, el) ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Scall(None, sg, c1, cl))
  | _ ->
      ignore (convert_rexpr e);
      prepend_seq !convert_accu Sskip

let mkassign id e =
  convert_accu := [];
  match e with
  | Rcall(sg, e1, el) ->
      let c1 = convert_rexpr e1 in
      let cl = convert_rexpr_list el in
      prepend_seq !convert_accu (Scall(Some id, sg, c1, cl))
  | _ ->
      let c = convert_rexpr e in
      prepend_seq !convert_accu (Sassign(id, c))

let mkstore chunk e1 e2 =
  convert_accu := [];
  let c1 = convert_rexpr e1 in
  let c2 = convert_rexpr e2 in
  prepend_seq !convert_accu (Sstore(chunk, c1, c2))

let mkifthenelse e s1 s2 =
  convert_accu := [];
  let c = convert_rexpr e in
  prepend_seq !convert_accu (Sifthenelse(c, s1, s2))

let mkreturn_some e =
  convert_accu := [];
  let c = convert_rexpr e in
  prepend_seq !convert_accu (Sreturn (Some c))

let mktailcall sg e1 el =
  convert_accu := [];
  let c1 = convert_rexpr e1 in
  let cl = convert_rexpr_list el in
  prepend_seq !convert_accu (Stailcall(sg, c1, cl))

(** Other constructors *)

let intconst n =
  Rconst(Ointconst(coqint_of_camlint n))

let andbool e1 e2 =
  Rcondition(e1, e2, intconst 0l)
let orbool e1 e2 =
  Rcondition(e1, intconst 1l, e2)

let exitnum n = nat_of_camlint(Int32.pred n)

let mkswitch expr (cases, dfl) =
  convert_accu := [];
  let c = convert_rexpr expr in
  let rec mktable = function
  | [] -> []
  | (key, exit) :: rem ->
      Coq_pair(coqint_of_camlint key, exitnum exit) :: mktable rem in
  prepend_seq !convert_accu (Sswitch(c, mktable cases, exitnum dfl))

(***
   match (a) { case 0: s0; case 1: s1; case 2: s2; }  --->

   block {
   block {
   block {
   block {
     switch(a) { case 0: exit 0; case 1: exit 1; default: exit 2; }
   }; s0; exit 2;
   }; s1; exit 1;
   }; s2;
   }

   Note that matches are assumed to be exhaustive
***)

let mkmatch_aux expr cases =
  let ncases = Int32.of_int (List.length cases) in
  let rec mktable n = function
    | [] -> assert false
    | [key, action] -> []
    | (key, action) :: rem ->
        Coq_pair(coqint_of_camlint key, nat_of_camlint n)
        :: mktable (Int32.succ n) rem in
  let sw =
    Sswitch(expr, mktable 0l cases, nat_of_camlint (Int32.pred ncases)) in
  let rec mkblocks body n = function
    | [] -> assert false
    | [key, action] ->
        Sblock(Sseq(body, action))
    | (key, action) :: rem ->
        mkblocks
          (Sblock(Sseq(body, Sseq(action, Sexit (nat_of_camlint n)))))
          (Int32.pred n)
          rem in
  mkblocks (Sblock sw) (Int32.pred ncases) cases

let mkmatch expr cases =
  convert_accu := [];
  let c = convert_rexpr expr in
  let s =
    match cases with
    | [] -> Sskip (* ??? *)
    | [key, action] -> action
    | _ -> mkmatch_aux c cases in
  prepend_seq !convert_accu s

%}

%token ABSF
%token AMPERSAND
%token AMPERSANDAMPERSAND
%token BANG
%token BANGEQUAL
%token BANGEQUALF
%token BANGEQUALU
%token BAR
%token BARBAR
%token CARET
%token CASE
%token COLON
%token COMMA
%token DEFAULT
%token DOLLAR
%token ELSE
%token EQUAL
%token EQUALEQUAL
%token EQUALEQUALF
%token EQUALEQUALU
%token EOF
%token EXIT
%token EXTERN
%token FLOAT
%token FLOAT32
%token FLOAT64
%token <float> FLOATLIT
%token FLOATOFINT
%token FLOATOFINTU
%token GREATER
%token GREATERF
%token GREATERU
%token GREATEREQUAL
%token GREATEREQUALF
%token GREATEREQUALU
%token GREATERGREATER
%token GREATERGREATERU
%token <AST.ident> IDENT
%token IF
%token IN
%token INT
%token INT16S
%token INT16U
%token INT32
%token INT8S
%token INT8U
%token <int32> INTLIT
%token INTOFFLOAT
%token INTUOFFLOAT
%token LBRACE
%token LBRACELBRACE
%token LBRACKET
%token LESS
%token LESSU
%token LESSF
%token LESSEQUAL
%token LESSEQUALU
%token LESSEQUALF
%token LESSLESS
%token LET
%token LOOP
%token LPAREN
%token MATCH
%token MINUS
%token MINUSF
%token MINUSGREATER
%token PERCENT
%token PERCENTU
%token PLUS
%token PLUSF
%token QUESTION
%token RBRACE
%token RBRACERBRACE
%token RBRACKET
%token RETURN
%token RPAREN
%token SEMICOLON
%token SLASH
%token SLASHF
%token SLASHU
%token STACK
%token STAR
%token STARF
%token <AST.ident> STRINGLIT
%token SWITCH
%token TILDE
%token TAILCALL
%token VAR
%token VOID

/* Precedences from low to high */

%left COMMA
%left p_let
%right EQUAL
%right QUESTION COLON
%left BARBAR
%left AMPERSANDAMPERSAND
%left BAR
%left CARET
%left AMPERSAND
%left EQUALEQUAL BANGEQUAL LESS LESSEQUAL GREATER GREATEREQUAL EQUALEQUALU BANGEQUALU LESSU LESSEQUALU GREATERU GREATEREQUALU EQUALEQUALF BANGEQUALF LESSF LESSEQUALF GREATERF GREATEREQUALF 
%left LESSLESS GREATERGREATER GREATERGREATERU
%left PLUS PLUSF MINUS MINUSF
%left STAR SLASH PERCENT STARF SLASHF SLASHU PERCENTU
%nonassoc BANG TILDE p_uminus ABSF INTOFFLOAT INTUOFFLOAT FLOATOFINT FLOATOFINTU INT8S INT8U INT16S INT16U FLOAT32 ALLOC
%left LPAREN

/* Entry point */

%start prog
%type <Cminor.program> prog

%%

/* Programs */

prog:
    global_declarations proc_list EOF
      { { prog_funct = List.rev $2;
          prog_main = intern_string "main";
          prog_vars = List.rev $1; } }
;

global_declarations:
    /* empty */                                 { [] }
  | global_declarations global_declaration      { $2 :: $1 }
;

global_declaration:
    VAR STRINGLIT LBRACKET INTLIT RBRACKET
      { Coq_pair($2, {gvar_info = (); gvar_init = [Init_space(z_of_camlint $4)];
                      gvar_readonly = false; gvar_volatile = false}) }
;

proc_list:
    /* empty */                                 { [] }
  | proc_list proc                              { $2 :: $1 }
;

/* Procedures */

proc:
    STRINGLIT LPAREN parameters RPAREN COLON signature
    LBRACE
      stack_declaration
      var_declarations
      stmt_list
    RBRACE
      { let tmp = !temporaries in
        temporaries := [];
        temp_counter := 0;
        Coq_pair($1,
        Internal { fn_sig = $6;
                   fn_params = List.rev $3;
                   fn_vars = List.rev (tmp @ $9);
                   fn_stackspace = $8;
                   fn_body = $10 }) }
  | EXTERN STRINGLIT COLON signature 
      { Coq_pair($2, External({ef_id = $2; ef_sig = $4; ef_inline = false})) }
;

signature:
    type_ 
               { {sig_args = []; sig_res = Some $1} }
  | VOID
               { {sig_args = []; sig_res = None} }
  | type_ MINUSGREATER signature
               { let s = $3 in {s with sig_args = $1 :: s.sig_args} }
;

parameters:
    /* empty */                                 { [] }
  | parameter_list                              { $1 }
;

parameter_list:
    IDENT                                       { $1 :: [] }
  | parameter_list COMMA IDENT                  { $3 :: $1 }
;

stack_declaration:
    /* empty */                                 { Z0 }
  | STACK INTLIT SEMICOLON                      { z_of_camlint $2 }
;

var_declarations:
    /* empty */                                 { [] }
  | var_declarations var_declaration            { $2 @ $1 }
;

var_declaration:
    VAR parameter_list SEMICOLON                { $2 }
;

/* Statements */

stmt:
    expr SEMICOLON                              { mkeval $1 }
  | IDENT EQUAL expr SEMICOLON                  { mkassign $1 $3 }
  | memory_chunk LBRACKET expr RBRACKET EQUAL expr SEMICOLON
                                                { mkstore $1 $3 $6 }
  | IF LPAREN expr RPAREN stmts ELSE stmts      { mkifthenelse $3 $5 $7 }
  | IF LPAREN expr RPAREN stmts                 { mkifthenelse $3 $5 Sskip }
  | LOOP stmts                                  { Sloop($2) }
  | LBRACELBRACE stmt_list RBRACERBRACE         { Sblock($2) }
  | EXIT SEMICOLON                              { Sexit O }
  | EXIT INTLIT SEMICOLON                       { Sexit (exitnum $2) }
  | RETURN SEMICOLON                            { Sreturn None }
  | RETURN expr SEMICOLON                       { mkreturn_some $2 }
  | SWITCH LPAREN expr RPAREN LBRACE switch_cases RBRACE
                                                { mkswitch $3 $6 }
  | MATCH LPAREN expr RPAREN LBRACE match_cases RBRACE
                                                { mkmatch $3 $6 }
  | TAILCALL expr LPAREN expr_list RPAREN COLON signature SEMICOLON
                                                { mktailcall $7 $2 $4 }
;

stmts:
    LBRACE stmt_list RBRACE                     { $2 }
  | stmt                                        { $1 }
;

stmt_list:
    /* empty */                                 { Sskip }
  | stmt stmt_list                              { Sseq($1, $2) }
;

switch_cases:
    DEFAULT COLON EXIT INTLIT SEMICOLON
           { ([], $4) }
  | CASE INTLIT COLON EXIT INTLIT SEMICOLON switch_cases
           { let (cases, dfl) = $7 in (($2, $5) :: cases, dfl) }
;

match_cases:
    /* empty */                                 { [] }
  | CASE INTLIT COLON stmt_list match_cases     { ($2, $4) :: $5 }
;

/* Expressions */

expr:
    LPAREN expr RPAREN                          { $2 }
  | IDENT                                       { Rvar $1 }
  | INTLIT                                      { intconst $1 }
  | FLOATLIT                                    { Rconst(Ofloatconst $1) }
  | STRINGLIT                                   { Rconst(Oaddrsymbol($1, Int.zero)) }
  | AMPERSAND INTLIT                            { Rconst(Oaddrstack(coqint_of_camlint $2)) }
  | MINUS expr    %prec p_uminus                { Runop(Onegint, $2) }
  | MINUSF expr   %prec p_uminus                { Runop(Onegf, $2) }
  | ABSF expr                                   { Runop(Oabsf, $2) }
  | INTOFFLOAT expr                             { Runop(Ointoffloat, $2) }
  | INTUOFFLOAT expr                            { Runop(Ointuoffloat, $2) }
  | FLOATOFINT expr                             { Runop(Ofloatofint, $2) }
  | FLOATOFINTU expr                            { Runop(Ofloatofintu, $2) }
  | TILDE expr                                  { Runop(Onotint, $2) }
  | BANG expr                                   { Runop(Onotbool, $2) }
  | INT8S expr                                  { Runop(Ocast8signed, $2) }
  | INT8U expr                                  { Runop(Ocast8unsigned, $2) }
  | INT16S expr                                 { Runop(Ocast16signed, $2) }
  | INT16U expr                                 { Runop(Ocast16unsigned, $2) }
  | FLOAT32 expr                                { Runop(Osingleoffloat, $2) }
  | expr PLUS expr                              { Rbinop(Oadd, $1, $3) }
  | expr MINUS expr                             { Rbinop(Osub, $1, $3) }
  | expr STAR expr                              { Rbinop(Omul, $1, $3) }
  | expr SLASH expr                             { Rbinop(Odiv, $1, $3) }
  | expr PERCENT expr                           { Rbinop(Omod, $1, $3) }
  | expr SLASHU expr                            { Rbinop(Odivu, $1, $3) }
  | expr PERCENTU expr                          { Rbinop(Omodu, $1, $3) }
  | expr AMPERSAND expr                         { Rbinop(Oand, $1, $3) }
  | expr BAR expr                               { Rbinop(Oor, $1, $3) }
  | expr CARET expr                             { Rbinop(Oxor, $1, $3) }
  | expr LESSLESS expr                          { Rbinop(Oshl, $1, $3) }
  | expr GREATERGREATER expr                    { Rbinop(Oshr, $1, $3) }
  | expr GREATERGREATERU expr                   { Rbinop(Oshru, $1, $3) }
  | expr PLUSF expr                             { Rbinop(Oaddf, $1, $3) }
  | expr MINUSF expr                            { Rbinop(Osubf, $1, $3) }
  | expr STARF expr                             { Rbinop(Omulf, $1, $3) }
  | expr SLASHF expr                            { Rbinop(Odivf, $1, $3) }
  | expr EQUALEQUAL expr                        { Rbinop(Ocmp Ceq, $1, $3) }
  | expr BANGEQUAL expr                         { Rbinop(Ocmp Cne, $1, $3) }
  | expr LESS expr                              { Rbinop(Ocmp Clt, $1, $3) }
  | expr LESSEQUAL expr                         { Rbinop(Ocmp Cle, $1, $3) }
  | expr GREATER expr                           { Rbinop(Ocmp Cgt, $1, $3) }
  | expr GREATEREQUAL expr                      { Rbinop(Ocmp Cge, $1, $3) }
  | expr EQUALEQUALU expr                       { Rbinop(Ocmpu Ceq, $1, $3) }
  | expr BANGEQUALU expr                        { Rbinop(Ocmpu Cne, $1, $3) }
  | expr LESSU expr                             { Rbinop(Ocmpu Clt, $1, $3) }
  | expr LESSEQUALU expr                        { Rbinop(Ocmpu Cle, $1, $3) }
  | expr GREATERU expr                          { Rbinop(Ocmpu Cgt, $1, $3) }
  | expr GREATEREQUALU expr                     { Rbinop(Ocmpu Cge, $1, $3) }
  | expr EQUALEQUALF expr                       { Rbinop(Ocmpf Ceq, $1, $3) }
  | expr BANGEQUALF expr                        { Rbinop(Ocmpf Cne, $1, $3) }
  | expr LESSF expr                             { Rbinop(Ocmpf Clt, $1, $3) }
  | expr LESSEQUALF expr                        { Rbinop(Ocmpf Cle, $1, $3) }
  | expr GREATERF expr                          { Rbinop(Ocmpf Cgt, $1, $3) }
  | expr GREATEREQUALF expr                     { Rbinop(Ocmpf Cge, $1, $3) }
  | memory_chunk LBRACKET expr RBRACKET         { Rload($1, $3) }
  | expr AMPERSANDAMPERSAND expr                { andbool $1 $3 }
  | expr BARBAR expr                            { orbool $1 $3 }
  | expr QUESTION expr COLON expr               { Rcondition($1, $3, $5) }
  | expr LPAREN expr_list RPAREN COLON signature{ Rcall($6, $1, $3) }
;

expr_list:
    /* empty */                                 { [] }
  | expr_list_1                                 { $1 }
;

expr_list_1:
    expr                     %prec COMMA        { $1 :: [] }
  | expr COMMA expr_list_1                      { $1 :: $3 }
;

memory_chunk:
    INT8S                                       { Mint8signed }
  | INT8U                                       { Mint8unsigned }
  | INT16S                                      { Mint16signed }
  | INT16U                                      { Mint16unsigned }
  | INT32                                       { Mint32 }
  | INT                                         { Mint32 }
  | FLOAT32                                     { Mfloat32 }
  | FLOAT64                                     { Mfloat64 }
  | FLOAT                                       { Mfloat64 }
;

/* Types */

type_:
    INT                                         { Tint }
  | FLOAT                                       { Tfloat }
;
