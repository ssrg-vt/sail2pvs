
open Output
open Typed_ast
open Typed_ast_syntax
open Target
open Types
open Backend_common
open Pvs_backend_utils

let print_and_fail l s =
  raise (Reporting_basic.err_general true l s)

let delim_regexp = Str.regexp "^\\([][`;,(){}]\\|;;\\)$"

let symbolic_regexp = Str.regexp "^[-!$%&*+./:<=>?@^|~]+$"

let is_delim s = Str.string_match delim_regexp s 0

let is_symbolic s = Str.string_match symbolic_regexp s 0

let is_abbreviation l =
  let length = Seplist.length l in
  let abbreviation =
    match Seplist.hd l with
      | (_, _, _, Te_abbrev _, _) -> true
      | _ -> false
  in
    length = 1 && abbreviation

let is_record l =
  let length = Seplist.length l in
  let record =
    match Seplist.hd l with
      | (_, _, _, Te_record _, _) -> true
      | _ -> false
  in
    length = 1 && record

let need_space x y =
  let f x =
    match x with
      | Kwd'(s) ->
      	if is_delim s then
          (true,false)
        else if is_symbolic s then
          (false,true)
        else
          (false,false)
      | Ident'(r) ->
        (false, is_symbolic @@ Ulib.Text.to_string r)
      | Num' _ ->
        (false,false)
  in
    let (d1,s1) = f x in
    let (d2,s2) = f y in
    not d1 && not d2 && s1 = s2

let handle_special_type x =
  let ts = output_to_string x in
  let new_ts = 
    if String.equal ts "unit" then "Unit" else ts in
  let comm_str = Str.regexp "(\*[A-Za-z0-9 ,.\n]+\*)" in
  let new_ts = Str.global_replace comm_str "" new_ts in
  from_string new_ts

let char_escape c = match int_of_char c with
  | 0x5c -> "\\\\" (* backslash *)
  | 0x22 -> "\\\"" (* double quote *)
  | 0x27 -> "\\\'" (* single quote *)
  | x when x >= 32 && x <= 126 -> (* other printable characters *)
      String.make 1 c
  | 0x07 -> "\\a" (* common control characters *)
  | 0x08 -> "\\b"
  | 0x09 -> "\\t"
  | 0x0a -> "\\n"
  | 0x0b -> "\\v"
  | 0x0c -> "\\f"
  | 0x0d -> "\\r"
  | x when x <= 255 ->
      Printf.sprintf "\\%03u" x
  | _ -> failwith "int_of_char returned an unexpected value"
  
let in_target targets = Typed_ast.in_targets_opt (Target.Target_no_ident Target.Target_pvs) targets;;

let pvs_infix_op a x =
  if (Ulib.Text.left x 1 = star || Ulib.Text.right x 1 = star) then
    from_string "(" ^ space ^ id a x ^ space ^ from_string ")"
  else
    from_string "(" ^ id a x ^ from_string ")"

let pvs_format_op use_infix =
  if use_infix then
    pvs_infix_op
  else
    id


module PvsBackendAux (A : sig val avoid : var_avoid_f option;; val env : env;; val dir : string;; val ascii_rep_set : Types.Cdset.t end) =
  struct

    module B = Backend_common.Make (
      struct
        let env = A.env
        let target = Target_no_ident Target_pvs
        let id_format_args = (pvs_format_op, path_sep)
        let dir = A.dir
      end);;

    module C = Exps_in_context (
      struct
        let env_opt = Some A.env
        let avoid = A.avoid
      end)
    ;;

    let fresh_name_counter = ref 0
    ;;

    let generate_fresh_name = fun () ->
      let old  = !fresh_name_counter in
      let _    = fresh_name_counter := old + 1 in
      let post = string_of_int old in
      from_string @@ Pervasives.(^) "x" post
    ;;

    let use_ascii_rep_for_const (cd : const_descr_ref id) : bool = Types.Cdset.mem cd.descr A.ascii_rep_set

    let typ_ident_to_output (p : Path.t id) = B.type_id_to_output p

    let field_ident_to_output fd = 
      Ident.to_output Term_field path_sep (B.const_id_to_ident fd (use_ascii_rep_for_const fd))

    let constant_application_to_output arg_f0 c_id args ascii_alternative given_id_opt = begin
      let arg_f b e = if b then arg_f0 (mk_opt_paren_exp e) else arg_f0 e in
      let (ascii_used, given_id_used, i) = B.const_id_to_ident_aux c_id ascii_alternative given_id_opt in 
      let const_is_infix = (not ascii_used) in 
      let is_infix = const_is_infix && (Ident.has_empty_path_prefix i) && (List.length args = 2) in           
      let use_infix_notation = ((not is_infix) && const_is_infix) in
      let name = B.ident_to_output use_infix_notation given_id_used i in
      let args_out = List.map (arg_f use_infix_notation) args in
      if (not is_infix) then
        (name :: args_out) 
      else 
        [(List.nth args_out 0); name; (List.nth args_out 1)]
    end
    ;;

    type variable
      = Tyvar of Output.t
      | Nvar of Output.t
    ;;

    let rec def_extra (callback: def list -> Output.t) (m: def_aux) =
      match m with
        | Lemma (skips, lemma_typ, targets, (name, _), skips', e) ->
          if in_target targets then
            let name = Name.to_output Term_var name in
	    let ty = Typed_ast.exp_to_typ e in
    	    let tv_set = match skips' with 
	      | Some([Ast.Com (Ast.Chars cstrs)]) -> 
		begin
		  let css = Str.split (Str.regexp ",") (Ulib.Text.to_string cstrs) in
		  let cs = List.map (string_to_const_descr_ref) css in
		  let l_unk = Ast.Trans (true, "lemma_def_extra", None) in
		  let cds = List.map (c_env_lookup l_unk A.env.c_env) cs in
		  let tnvars = List.flatten (List.map (fun cd -> cd.const_tparams) cds) in
		  let tvset = List.fold_left (fun s x -> TNset.add x s) TNset.empty tnvars in
		  type_variables true tvset
		end
	      | _ -> emp in
              Output.flat [
                name; tv_set; space; from_string ":"; space; from_string "LEMMA"; space; exp e; new_line; new_line
              ]
          else
            from_string "% [?]: Removed lemma intended for another backend."
        | _ -> emp
    and def (callback : def list -> Output.t) (m : def_aux) =
      match m with
      | Type_def (skips, def) ->
          let funcl =	if is_abbreviation def then
        		  type_def_abbreviation
        		else if is_record def then
        		  type_def_record
        		else
        		  type_def
          in
            Output.flat [
              comment_output (ws skips); new_line; funcl def; new_line; new_line
            ]
      | Val_def (def) ->
          let tv_set = val_def_get_free_tnvars A.env def in
          val_def None (snd (Typed_ast_syntax.is_recursive_def m)) def tv_set
      | Module (skips, (name, l), mod_binding, skips', skips'', defs, skips''') ->
        let name = Name.to_output Term_var name in
        let body = callback defs in
          Output.flat [
            name; from_string " : "; from_string "THEORY\nBEGIN\n"; ws skips'; ws skips'';
            body; from_string "\nEnd "; name
          ]
      | Rename (skips, (n,l), mod_binding, skips', mod_descr) -> Name.to_output Module_name n
      | OpenImport (oi, ms) ->                  
          let (ms', sk) = B.open_to_open_target ms in
          if (ms' = []) then
             ws (oi_get_lskip oi)
          else (
            let d' = OpenImportTarget(oi, Targets_opt_none, ms') in
            def callback d' ^ ws sk
          )
      | OpenImportTarget(oi, _, []) -> ws (oi_get_lskip oi)
      | OpenImportTarget (Ast.OI_open skips, targets, mod_descrs) ->                 
          let handle_mod (sk, md) = begin
            Output.flat [
              from_string "IMPORTING"; ws sk; from_string md; new_line; new_line
            ]
          end in
          if (not (in_target targets)) then emp else Output.flat (List.map handle_mod mod_descrs)
      | OpenImportTarget _ -> emp
      | Indreln (skips, targets, names, cs) -> from_string "\n% [?]: removed inductive relations.\n"
      | Val_spec val_spec -> from_string "\n% [?]: removed value specification.\n"
      | Class (Ast.Class_inline_decl (skips, _), _, _, _, _,_, _, _) -> from_string "\n% [?]: inline class declaration is commented out.\n"
      | Class (Ast.Class_decl skips, skips', (name, l), tv, p, skips'', body, skips''') -> from_string "\n% [?]: class type is transformed to record type.\n"
      | Instance (Ast.Inst_default skips, i_ref, inst, vals, skips') -> emp
      | Instance (Ast.Inst_decl skips, i_ref, inst, vals, skips') -> emp
      | Comment c ->
      	let ((def_aux, _), l, lenv) = c in
          Output.flat [
            new_line; from_string "% "; comment_output (def callback def_aux); new_line
          ]
      | _ -> emp
    and val_def i_ref_opt is_recursive def tv_set =
      begin
        match def with
          | Let_def (skips, targets, (p, name_map, topt, sk, e)) -> from_string "\n% [?]: simple let_defs are turned into fun_def .\n"
          | Fun_def (skips, _, targets, funcl_skips_seplist) ->
              if in_target targets then
                let funcls = Seplist.to_list funcl_skips_seplist in
                let bodies = List.map (funcl i_ref_opt tv_set is_recursive) funcls in
                let formed = concat_str "\n" bodies in
                  Output.flat [
                    comment_output (ws skips); new_line; formed; new_line; new_line
                  ]
              else
                from_string "\n% [?]: removed recursive definition intended for another target.\n"
          | _ -> from_string "\n% [?]: removed top-level value definition.\n"
      end
    and let_body i_ref_opt top_level tv_set is_recursive ((lb, _):letbind) =
      match lb with
        | Let_val (p, topt, skips, e) ->
            let p = def_pattern p in
            let tv_set =
              if Types.TNset.cardinal tv_set = 0 then
                let typ = Typed_ast.exp_to_typ e in
                Types.free_vars typ
              else
                tv_set
            in
            let tv_set = type_variables top_level tv_set in
              Output.flat [
                p; tv_set; space; from_string "="; space; exp e
              ]
        | Let_fun (n, pats, typ_opt, skips, e) ->
          funcl_aux i_ref_opt tv_set is_recursive (n.term, pats, typ_opt, skips, e)
    and funcl_aux i_ref_opt tv_set is_recursive (n, pats, typ_opt, skips, e) =
      let name_skips = Name.get_lskip n in
      let name = from_string (Name.to_string (Name.strip_lskip n)) in
      let tv_set =
        if Types.TNset.cardinal tv_set = 0 then
          let typ = Typed_ast.exp_to_typ e in
          let tv_set = Types.free_vars typ in
            type_variables true tv_set
        else
          type_variables true tv_set
      in
      let return_typ =
        match typ_opt with
          | None -> emp
          | Some (s, t) -> typ t
      in
      if is_recursive then
	Output.flat [
          comment_output (ws name_skips); new_line; 
	  name; tv_set; 
          pat_list pats; space; from_string ":"; space; from_string "RECURSIVE"; space; return_typ; 
	  from_string " = "; exp e; new_line
        ]
      else
	Output.flat [
          comment_output (ws name_skips); new_line; 
	  name; tv_set;
          pat_list pats; space; from_string ":"; space; return_typ; 
	  from_string " = "; exp e; new_line
        ]
    and funcl i_ref_opt tv_set is_recursive ({term = n}, c, pats, typ_opt, skips, e) =
      let n = B.const_ref_to_name n true c
      in
        funcl_aux i_ref_opt tv_set is_recursive (n, pats, typ_opt, skips, e)
    and type_variables top_level tv_set =
      if Types.TNset.is_empty tv_set || not top_level then
        emp
      else
      let tyvars =
        List.map (fun tv -> match tv with
          | Types.Ty tv -> id Type_var (tyvar_to_upper tv)
          | Types.Nv nv -> id Type_var (nvar_to_upper nv)) (*TODO This may not be how the length variables should be represented, so should be checked on *)
        (Types.TNset.elements tv_set)
      in
        if List.length tyvars = 0 || not top_level then
          emp
        else
	  Output.flat [
	    from_string "["; concat_str ", " tyvars; space; from_string ":"; space; from_string "TYPE"; from_string "]"
	  ]
    and exp e =
      let is_user_exp = Typed_ast_syntax.is_pp_exp e in
        match C.exp_to_term e with
          | Var v ->
              Name.to_output Term_var v
          | Backend (sk, i) ->
	      Ident.to_output (Term_const (false, true)) path_sep i
          | Lit l -> literal l
          | Do (skips, mod_descr_id, do_line_list, skips', e, skips'', type_int) -> assert false (* DPM: should have been removed by macros *)
          | App (e1, e2) ->
              let trans e = block (Typed_ast_syntax.is_pp_exp e) 0 (exp e) in
              let sep = emp in
              let oL = begin
              (* try to strip all application and see whether there is a constant at the beginning *)
              let (e0, args) = strip_app_exp e in
                match C.exp_to_term e0 with
                  | Constant cd -> 
                    (* constant, so use special formatting *)
		    (let c_descr = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
		    match Target.Targetmap.apply_target c_descr.target_rep (Target_no_ident Target_pvs) with
		      | Some (CR_infix (_, _, _, i)) -> 
			let args = constant_application_to_output trans cd args (use_ascii_rep_for_const cd) (Some i) in
			Output.concat (space) args
		      | _ -> 
			let args = B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd) in
			constr_fun_app sep args)
                  | _ -> (* no constant, so use standard one *)
                    constr_fun_app sep (List.map trans (e0::args))
              end in
              block is_user_exp 0 oL
          | Paren (skips, e, skips') -> exp e
          | Typed (skips, e, skips', t, skips'') -> exp e
             (* Output.flat [
                from_string "("; exp e; space; from_string ":"; space; typ t; from_string ")";
              ]*)
          | Tup (skips, es, skips') ->
              let tups = flat @@ Seplist.to_sep_list exp (fun s -> from_string ", ") es in
                Output.flat [
                  from_string "("; tups; from_string ")"
                ]
          | List (skips, es, skips') ->
	      let lists = Seplist.to_list_map (fun x -> from_string "cons(" ^ exp x ^ from_string ", ") es in
	      if Seplist.is_empty es then
	        from_string "null"
	      else
		let body = flat @@ lists in
                Output.flat [
                  body; from_string "null"; from_string (String.make (List.length lists) ')')
                ]
          | Let (skips, bind, skips', e) ->
              let body = let_body None false Types.TNset.empty false bind in
                Output.flat [
                  from_string "LET"; space; body; space; from_string "IN"; space; exp e
                ]
          | Constant const ->
	    Output.concat emp (B.function_application_to_output (exp_to_locn e) exp false e const [] (use_ascii_rep_for_const const))
          | Fun (skips, ps, skips', e) ->
	      let pt = pat_list ps in
	      Output.flat [
                  from_string "("; from_string "LAMBDA"; space; pt; space; from_string ":"; space; exp e; from_string ")"
                ]
          | Function _ ->
            (* DPM: should have been macro'd away *)
              print_and_fail (Typed_ast.exp_to_locn e) "illegal function in extraction, should have been previously macro'd away"
          | Set (skips, es, skips') ->
            if Seplist.is_empty es then
              from_string "emptyset"
            else
	      let name = generate_fresh_name () in
	      let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (fun e -> name ^ from_string " = " ^ (exp e)) (fun s -> from_string " OR ") es in
	      let t = Typed_ast.exp_to_typ (Seplist.hd es) in
	      let ty = typ @@ C.t_to_src_t t in
	      block is_user_exp 0 (
                  Output.flat [
                    from_string "{"; space; name; from_string " : "; ty; space; from_string "|"; space; body; space; from_string "}"
                  ])
          | Begin (skips, e, skips') -> exp e
          | Record (skips, fields, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) field_update (fun s -> from_string ",") fields in
              Output.flat [
                from_string "(#"; body; new_line; new_line; from_string "#)"; new_line
              ]
          | Field (e, skips, fd) ->
            let name = field_ident_to_output fd in
              Output.flat [
                exp e; from_string "`"; name
              ]
          | Recup (skips, e, skips', fields, skips'') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) field_update (sep @@ from_string ",") fields in
              Output.flat [
                 from_string "("; exp e; from_string "(#"; body; new_line; new_line; from_string "#))"
              ]
          | Case (_, skips, e, skips', cases, skips'') ->
            let body = case_concat (from_string ",") @@ Seplist.to_list_map (fun c -> new_line ^ identation ^ case_line c) cases in
              Output.flat [
                new_line; from_string "CASES"; space; exp e; space; from_string "OF";
		body; space; new_line;
		from_string "ENDCASES"
              ]
          | Infix (l, c, r) ->
              let trans e = block (Typed_ast_syntax.is_pp_exp e) 0 (exp e) in
              let sep = space in
              begin
                match C.exp_to_term c with
                  | Constant cd -> 
                    begin
                      let pieces = B.function_application_to_output (exp_to_locn e) trans true e cd [l ; r] (use_ascii_rep_for_const cd) in
                      Output.concat sep pieces
                    end
                  | _           ->
                    begin
                      let mapped = List.map trans [l; c; r] in
                      Output.concat sep mapped
                    end
              end
          | If (skips, test, skips', t, skips'', f) ->
              block true 0 (Output.flat [
                break_hint_space 2; from_string "IF"; break_hint_space 1;
                block (Typed_ast_syntax.is_pp_exp test) 0 (exp test);
                break_hint_space 2; from_string "THEN"; break_hint_space 1;
                block (Typed_ast_syntax.is_pp_exp t) 0 (exp t);
                break_hint_space 2; from_string "ELSE"; break_hint_space 1;
                block (Typed_ast_syntax.is_pp_exp f) 0 (exp f); 
	        break_hint_space 2; from_string "ENDIF"
              ])
          | Quant (quant, quant_binding_list, skips, e) ->
            (* XXX: this should only appear in the context of a lemma or theorem statement,
             *      and should have been macro'd away hopefully elsewhere.
             *)
            let quant =
              match quant with
                | Ast.Q_forall _ -> from_string "FORALL"
                | Ast.Q_exists _ -> from_string "EXISTS"
            in
            let bindings =
              Output.concat (from_string ", ") (
                List.map (fun quant_binding ->
                  match quant_binding with
                    | Typed_ast.Qb_var name_lskips_annot ->
                      let name = name_lskips_annot.term in
		      let t = name_lskips_annot.typ in
		      let src_t = C.t_to_src_t t in
		      let v_typ = typ src_t in
                      let name = from_string @@ Ulib.Text.to_string @@ Name.to_rope @@ Name.strip_lskip name in
                        Output.flat [
			  from_string "("; name; space; from_string ":"; space; v_typ; from_string ")"
			]
                    | Typed_ast.Qb_restr (bool, skips, pat, skips', e, skips'') ->
                      let pat_out = fun_pattern pat in
                        pat_out
                ) quant_binding_list)
            in
	    let quant_filterd = 
		(List.filter (fun quant_binding ->
                  match quant_binding with
                    | Typed_ast.Qb_var name_lskips_annot -> false
                    | Typed_ast.Qb_restr (bool, skips, pat, skips', e, skips'') -> true
                ) quant_binding_list)
	    in
	    let binding_extra = if List.length quant_filterd > 0 then
              (Output.concat (from_string " AND ") (
		List.map (fun quant_binding ->
                  match quant_binding with
                    | Typed_ast.Qb_var name_lskips_annot -> from_string ""
                    | Typed_ast.Qb_restr (bool, skips, pat, skips', e, skips'') ->
                      let pat_out = def_pattern pat in
                        Output.flat [
                          from_string "member"; from_string "("; pat_out; from_string ")"; from_string "("; exp e; from_string ")"
                        ]
                ) quant_filterd)) ^ (from_string " IMPLIES ") else (from_string "")
            in
              Output.flat [
                quant; space; bindings; space; from_string ":"; space; binding_extra;
                from_string "("; exp e; from_string ")"
              ]
          | Comp_binding (_, _, _, _, _, _, _, _, _) -> from_string "% XXX: comp binding"
          | Setcomp (_, _, _, _, _, _) -> from_string "% XXX: setcomp"
          | Nvar_e (skips, nvar) ->
            let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r "") (Nvar.to_rope nvar) in
              nvar
          | VectorAcc (e, skips, nexp, skips') ->
              Output.flat [
                exp e; from_string "("; src_nexp nexp; from_string ")"
              ]
          | VectorSub (e, skips, nexp, skips', nexp', skips'') ->
              Output.flat [
                exp e; from_string "^"; from_string "("; src_nexp nexp'; from_string ","; space;
                src_nexp nexp; from_string ")"
              ]
          | Vector (skips, es, skips') ->
	    (* The order of elements of bit vector in pvs and lem are different*)
            let body = flat @@ List.rev @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) exp (fun s -> emp) es in
              block is_user_exp 0 (
                if Seplist.is_empty es then
                  from_string "empty_bv"
                else
		  let length = string_of_int (Seplist.length es) in
                  Output.flat [
                    from_string "bv"; from_string "["; from_string length; from_string "]"; from_string "("; from_string "0b"; body; from_string ")"
                  ])
    and src_nexp n =
      match n.nterm with
        | Nexp_var (skips, nvar) ->
          let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r"") (Nvar.to_rope nvar) in
            nvar
        | Nexp_const (skips, i) -> from_string (string_of_int i)
        | Nexp_mult (nexp, skips, nexp') ->
            Output.flat [
              src_nexp nexp; space; from_string "*"; space; src_nexp nexp'
            ]
        | Nexp_add (nexp, skips, nexp') ->
            Output.flat [
              src_nexp nexp; space; from_string "+"; space; src_nexp nexp'
            ]
        | Nexp_paren (skips, nexp, skips') ->
            src_nexp nexp
    and case_line (p, skips, e, _) =
        match p.term with
        | P_wild skips ->
		Output.flat [
		  from_string "ELSE"; space; exp e
		]
	| _ ->
		Output.flat [
		  def_pattern p; from_string ":"; space; exp e
		]
    and field_update (fd, skips, e, _) =
      let name = field_ident_to_output fd in
        Output.flat [
          identation; name; space; from_string ":="; space; exp e
        ]
    and literal l =
      match l.term with
        | L_true skips -> from_string "TRUE"
        | L_false skips -> from_string "FALSE"
        | L_num (skips, n, _) -> num n
        | L_string (skips, s, s_org) ->
	    let escaped = Util.option_default (String.escaped s) s_org in
	    meta (String.concat "" ["\""; escaped; "\""])
        | L_unit (skips, skips') -> from_string "unit"
        | L_zero s -> from_string "0"
        | L_one s -> from_string "1"
        | L_char (s, c, c_org) ->
	  let escaped = Util.option_default (char_escape c) c_org in
          meta (String.concat "" ["\""; escaped; "\""; "("; "0"; ")"])
        | L_numeral (skips, i, _) -> from_string @@ string_of_int i
        | L_vector (s, v, v') -> assert false
        | L_undefined (skips, explanation) ->
          let typ = l.typ in
          let src_t = C.t_to_src_t typ in
            Output.flat [
              from_string "% "; from_string (comment_string explanation)
            ]
    and pat_list ps = (concat_str "" @@ List.map fun_pattern ps)
    and fun_pattern p =
      match p.term with
        | P_wild skips ->
          let t = C.t_to_src_t p.typ in
	  let name = generate_fresh_name () in
            Output.flat [
              from_string "("; name; space; from_string ":"; space; typ t; from_string ")"
            ]
        | P_var v ->
          let name = Name.to_output Term_var v in
          let t = C.t_to_src_t p.typ in
            Output.flat [
              from_string "("; name; space; from_string ":"; space; typ t; from_string ")"
            ]
        | P_lit l -> literal l
        | P_as (skips, p, skips', (n, l), skips'') ->
          let name = Name.to_output Term_var n in
            Output.flat [
              from_string "("; fun_pattern p; space; from_string "as pattern in PVS"; ws skips'; name; from_string "("
            ]
        | P_typ (skips, p, skips', t, skips'') ->
            Output.flat [
              from_string "("; def_pattern p; space; from_string ":"; space; typ t; from_string ")"
            ]
        | P_tup (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list fun_pattern (fun s -> from_string ", ") ps in
            Output.flat [
              from_string "("; body; from_string ")"
            ]
        | P_record (_, fields, _) ->
          (* DPM: should have been macro'd away *)
            print_and_fail p.locn "illegal record pattern in code extraction, should have been compiled away"
        | P_cons (p1, skips, p2) ->
            Output.flat [
              from_string "cons"; from_string "("; def_pattern p1; from_string ","; space; def_pattern p2; from_string ")"
            ]
        | P_var_annot (n, t) ->
            let name = Name.to_output Term_var n in
              Output.flat [
                from_string "("; name; space; from_string ":"; space; typ t; from_string ")"
              ]
        | P_list (skips, ps, skips') ->
	    let lists = Seplist.to_list_map (fun x -> from_string "cons(" ^ fun_pattern x ^ from_string ", ") ps in
	    if List.length lists = 0 then
	      from_string "null"
	    else
              let body = flat @@ lists in
                Output.flat [
                  body; from_string "null"; from_string (String.make (List.length lists) ')')
                ]
        | P_paren (skips, p, skips') -> fun_pattern p
        | P_const(cd, ps) ->
            let oL = B.pattern_application_to_output p.locn fun_pattern cd ps (use_ascii_rep_for_const cd) in
            concat emp oL
        | P_backend(sk, i, _, ps) ->
	    let body = 
	      if List.length ps = 0 then emp
	      else from_string "(" ^ concat_str ", " (List.map fun_pattern ps) ^ from_string ")" in
            Ident.to_output (Term_const (false, true)) path_sep i ^ body
        | P_num_add ((name, l), skips, skips', k) ->
            let succs = Output.flat @@ Util.replicate k (from_string "succ(") in
            let close = Output.flat @@ Util.replicate k (from_string ")") in
            let name = Name.to_output Term_var name in
              Output.flat [
                succs; name; close
              ]
        | _ -> from_string "% XXX: todo"
    and def_pattern p =
      match p.term with
        | P_wild skips -> 
	  generate_fresh_name ()
        | P_var v -> Name.to_output Term_var v
        | P_lit l -> literal l
        | P_as (skips, p, skips', (n, l), skips'') ->
          let name = Name.to_output Term_var n in
            Output.flat [
              from_string "("; def_pattern p; ws skips'; from_string "as pattern in PVS"; ws skips'; name; from_string ")"
            ]
        | P_typ (skips, p, _, t, skips') ->
            (* DPM: type restriction not allowed in Coq *)
            def_pattern p
        | P_tup (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list def_pattern (fun s -> from_string ", ") ps in
            Output.flat [
              from_string "("; body; from_string ")"
            ]
        | P_record (_, fields, _) ->
            (* DPM: should have been macro'd away *)
            print_and_fail p.locn "illegal record pattern in code extraction, should have been compiled away"
        | P_cons (p1, skips, p2) ->
            Output.flat [
              from_string "cons"; from_string "("; def_pattern p1; from_string ","; space; def_pattern p2; from_string ")"
            ]
        | P_var_annot (n, t) ->
          (* DPM: type restriction not allowed in Coq *)
            Name.to_output Term_var n
        | P_list (skips, ps, skips') ->
	    let lists = Seplist.to_list_map (fun x -> from_string "cons(" ^ def_pattern x ^ from_string ", ") ps in
	    if List.length lists = 0 then
	      from_string "null"
	    else
              let body = flat @@ lists in
                Output.flat [
                  body; from_string "null"; from_string (String.make (List.length lists) ')')
                ]
        | P_paren (skips, p, skips') ->
            def_pattern p
        | P_const(cd, ps) ->
            let oL = B.pattern_application_to_output p.locn def_pattern cd ps (use_ascii_rep_for_const cd) in
            concat emp oL
        | P_backend(sk, i, _, ps) ->
            let body = 
	      if List.length ps = 0 then emp
	      else from_string "(" ^ concat_str ", " (List.map def_pattern ps) ^ from_string ")" in
            Ident.to_output (Term_const (false, true)) path_sep i ^ body
        | P_num_add ((name, l), skips, skips', k) ->
            let succs = Output.flat @@ Util.replicate k (from_string "succ(") in
            let close = Output.flat @@ Util.replicate k (from_string ")") in
            let name = Name.to_output Term_var name in
              Output.flat [
                succs; name; close
              ]
        | _ -> from_string "% XXX: todo"
    and type_def_abbreviation def =
    	match Seplist.hd def with
    		| ((n, _), tyvars, path, Te_abbrev (skips, t),_) ->
            let n = B.type_path_to_name n path in
    	    let name = Name.to_output (Type_ctor (false, false)) n in
            let tyvars' = type_def_type_variables tyvars in
            let body = typ t in
              Output.flat [
    		name; tyvars'; from_string " : TYPE = "; body; new_line
    	      ]
    		| _ -> from_string "% Internal Lem error, please report."
    and type_def_record def =
    	match Seplist.hd def with
      	| (n, tyvars, path, (Te_record (skips, skips', fields, skips'') as r),_) ->
            let (n', _) = n in
            let n' = B.type_path_to_name n' path in
            let name = Name.to_output (Type_ctor (false, false)) n' in
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) field (sep @@ from_string ",") fields in
      	    let tyvars' = type_def_type_variables tyvars in
      	    Output.flat [
                name; tyvars'; from_string " : TYPE";
                space; from_string "="; space; from_string "[# ";
                body; new_line; from_string " #]"; new_line
   	    ]
        | _ -> from_string "% Internal Lem error, please report."
    and type_def defs =
      let body = flat @@ Seplist.to_sep_list type_def' (fun s -> from_string "OF") defs in
        Output.flat [
          body; new_line;
        ]
    and type_def' ((n0, l), ty_vars, t_path, ty, _) =
      let n = B.type_path_to_name n0 t_path in 
      let name = Name.to_output (Type_ctor (false, false)) n in
      let ty_vars =
        List.map (
          function
            | Typed_ast.Tn_A (_, tyvar, _) -> Tyvar (from_string @@ String.uppercase (Ulib.Text.to_string tyvar))
            | Typed_ast.Tn_N (_, nvar, _) -> Nvar (from_string @@ String.uppercase (Ulib.Text.to_string nvar))
          ) ty_vars
      in
        match ty with
	  | Te_opaque ->
	      let ty_var_sep = if List.length ty_vars = 0 then emp else space in
	      let ty_vars = inductive_type_variables ty_vars in
              Output.flat [
                name; ty_var_sep; ty_vars; from_string ": TYPE"
              ]
          | Te_variant (skips, ctors) ->
            Output.flat [
              inductive ty_vars name; tyexp name ty_vars ty; from_string "\nEND "; name
            ]
	  | _ -> emp
    and inductive ty_vars name =
      let ty_var_sep = if List.length ty_vars = 0 then emp else space in
      let ty_vars = inductive_type_variables ty_vars in
        Output.flat [
          name; ty_var_sep; ty_vars; from_string " : DATATYPE\nBEGIN\n"
        ]
    and inductive_type_variables vars =
      let mapped = List.map (fun v ->
          match v with
            | Tyvar x ->
              Output.flat [
                x; from_string " : TYPE"
              ]
            | Nvar x ->
              Output.flat [
                x; from_string " : nat"
              ]) vars
      in
      let concat_mapped = concat_str ", " mapped in
      if List.length vars > 1 then
      	  Output.flat [from_string "["; concat_mapped; from_string "]"]
      else
	  concat_mapped
    and tyexp name ty_vars =
      function
        | Te_opaque -> emp
        | Te_abbrev (skips, t) -> tyexp_abbreviation t
        | Te_record (skips, _, fields, skips') -> tyexp_record fields
        | Te_variant (skips, ctors) ->
          let body = flat @@ Seplist.to_sep_list_first Seplist.Optional (constructor name ty_vars) (sep @@ new_line) ctors in
            body
    and constructor ind_name (ty_vars : variable list) ((name0, _), c_ref, skips, args) =
      let ctor_name = B.const_ref_to_name name0 false c_ref in
      let ctor_name = Name.to_output (Type_ctor (false, false)) ctor_name in
      let body = flat @@ Seplist.to_sep_list (fun x -> generate_fresh_name () ^ from_string ": " ^ typ x) (fun s -> from_string ", ") args in
      let ty_vars_typeset =
        concat_str ", " @@ List.map (fun v ->
          match v with
            | Tyvar out -> out
            | Nvar out -> out
        ) ty_vars
      in
        if Seplist.length args = 0 then
          Output.flat [
            break_hint_space 4; ctor_name; from_string ": "; ctor_name ; from_string "?"; ty_vars_typeset
          ]
        else
          Output.flat [
            break_hint_space 4; ctor_name; from_string "("; body; from_string ")"; from_string ": "; ctor_name; from_string "?"
          ]
    and tyexp_abbreviation t = from_string "% tyexp_abbreviation"
    and tyexp_record fields = from_string "% tyexp_record"
    and typ t =
      match t.term with
        | Typ_wild skips -> assert false (* should have been declared *)
        | Typ_var (skips, v) -> id Type_var @@ tyvar_to_upper v
        | Typ_fn (t1, skips, t2) -> from_string "[" ^ typ t1 ^ space ^ from_string "->" ^ space ^ typ t2 ^ from_string "]"
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list typ (fun s -> from_string ", ") ts in
              from_string "[" ^ body ^ from_string "]"
        | Typ_app (p, ts) ->
            let (ts, head) = B.type_app_to_output typ p ts in
	    let head = handle_special_type head in
	    let ts = List.map typ ts in
	    if List.length ts > 0 then
	      let ts = concat_str ", " ts in
	      Output.flat [
		head; from_string "["; ts; from_string "]"
	      ]
	    else
              head
        | Typ_paren(skips, t, skips') -> typ t
        | Typ_with_sort(t,_) -> raise (Reporting_basic.err_general true t.locn "Target sort annotations not currently supported for Pvs")
        | Typ_len nexp -> src_nexp nexp
        | Typ_backend (p, ts) ->
          let i = Path.to_ident (ident_get_lskip p) p.descr in
          let i = Ident.to_output (Type_ctor (false, true)) path_sep i in
	  if List.length ts > 0 then
            let ts = concat emp @@ List.map typ ts in
            Output.flat [
              i; from_string "["; ts; from_string "]"
            ]
	  else i
    and type_def_type_variables tvs =
      match tvs with
        | [] -> emp
        | [Typed_ast.Tn_A tv] -> from_string "[" ^ tyvar tv ^ from_string ": TYPE]"
        | tvs ->
          let mapped = List.map (fun t ->
            match t with
              | Typed_ast.Tn_A (_, tv, _) ->
                let tv = from_string @@ String.uppercase (Ulib.Text.to_string tv) in
                  Output.flat [
                    tv; from_string ": TYPE"
                  ]
              | Typed_ast.Tn_N nv ->
                  Output.flat [
                    from_string "nv: nat"
                  ]) tvs
          in
            Output.flat [
              from_string "["; concat_str ", " mapped; from_string "]"
            ]
    and field ((n, _), f_ref, skips, t) =
      Output.flat [
          Name.to_output Term_field (B.const_ref_to_name n false f_ref); 
          from_string ": "; typ t
      ]
      ;;
end
;;


module CdsetE = Util.ExtraSet(Types.Cdset)

module PvsBackend (A : sig val avoid : var_avoid_f option;; val env : env;; val dir : string end) =
  struct

    let rec defs (ds : def list) =
      	List.fold_right (fun (((d, s), l, lenv):def) y ->
          let ue = add_def_entities (Target_no_ident Target_pvs) true empty_used_entities ((d,s),l,lenv) in
          let callback = defs in
          let module C = PvsBackendAux (
            struct
              let avoid = A.avoid;;
              let env = {A.env with local_env = lenv};;
              let ascii_rep_set = CdsetE.from_list ue.used_consts;;
              let dir = A.dir;;
            end)
          in
          let (before_out, d') = Backend_common.def_add_location_comment ((d,s),l,lenv) in
          before_out ^ 
          match s with
            | None   -> C.def callback d' ^ y
            | Some s -> C.def callback d' ^ ws s ^ y
      	) ds emp
    and defs_extra (ds: def list) =
        List.fold_right (fun (((d, s), l, lenv):def) y ->
          let ue = add_def_entities (Target_no_ident Target_pvs) true empty_used_entities ((d,s),l,lenv) in
          let module C = PvsBackendAux (
            struct
              let avoid = A.avoid;;
              let env = {A.env with local_env = lenv};;
              let ascii_rep_set = CdsetE.from_list ue.used_consts;;
              let dir = A.dir;;
            end)
          in
          let callback = defs in
          match s with
            | None   -> C.def_extra callback d ^ y
            | Some s -> C.def_extra callback d ^ ws s ^ y
        ) ds emp
    ;;

    let pvs_defs ((ds : def list), end_lex_skips) =
      let pvs_defs = defs ds in
      let pvs_defs_extra = defs_extra ds in
    	  ((to_rope (r"\"") lex_skip need_space @@ pvs_defs ^ ws end_lex_skips),
          to_rope (r"\"") lex_skip need_space @@ pvs_defs_extra ^ ws end_lex_skips)
    ;;
  end
