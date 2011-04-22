(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Generic program transformation *)

open C
open Cutil
open Env

(* Recording fresh temporaries *)

let temporaries = ref ([]: decl list)

let reset_temps () =
  temporaries := []

let new_temp_var ?(name = "t") ty =
  let id = Env.fresh_ident name in
  temporaries := (Storage_default, id, ty, None) :: !temporaries;
  id

let new_temp ?(name = "t") ty =
  let id = new_temp_var ~name ty in
  { edesc = EVar id; etyp = ty }

let get_temps () =
  let temps = !temporaries in
  temporaries := [];
  List.rev temps

(* Generic transformation *)

let program
    ?(decl = fun env d -> d)
    ?(fundef = fun env fd -> fd)
    ?(composite = fun env su id fl -> fl)
    ?(typedef = fun env id ty -> ty)
    p =

  let rec transf_globdecls env accu = function
  | [] -> List.rev accu
  | g :: gl ->
      let (desc', env') =
        match g.gdesc with
        | Gdecl((sto, id, ty, init) as d) ->
           (Gdecl(decl env d), Env.add_ident env id sto ty)
        | Gfundef f ->
           (Gfundef(fundef env f),
            Env.add_ident env f.fd_name f.fd_storage (fundef_typ f))
        | Gcompositedecl(su, id) ->
            (Gcompositedecl(su, id),
             Env.add_composite env id (composite_info_decl env su))
        | Gcompositedef(su, id, fl) ->
            (Gcompositedef(su, id, composite env su id fl),
             Env.add_composite env id (composite_info_def env su fl))
        | Gtypedef(id, ty) ->
            (Gtypedef(id, typedef env id ty), Env.add_typedef env id ty)
        | Genumdef _ as gd -> (gd, env)
        | Gpragma _ as gd -> (gd, env)
      in
        transf_globdecls env' ({g with gdesc = desc'} :: accu) gl

  in transf_globdecls (Builtins.environment()) [] p
