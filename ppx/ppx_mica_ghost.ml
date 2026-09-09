(** The erasing rewriter for Mica's ghost fragment.

   Mica reads the ghost syntax for proof-only instructions. The rewriter deletes
   the ghost annotations as follows:
   {[
     let%ghost x = e in body       ==>  body
     let f x = e [@@ghost]         ==>  (deleted)
     let f x = e [@@ghost (h : t)] ==>  let f x = e
     (f a [@ghost g])              ==>  (f a)
   ]}

   The other Mica attributes ([@@spec], [@@fn], [@@impl], [@@decreases]) stay:
   OCaml ignores them, and they annotate code that survives erasure. *)

open Ppxlib

let ghost = "ghost"

let is_ghost attr = String.equal attr.attr_name.txt ghost

(* An empty payload marks the whole declaration ghost. A payload declares the
   ghost parameters of a declaration that stays. *)
let is_whole_ghost attr =
  is_ghost attr && match attr.attr_payload with PStr [] -> true | _ -> false

let is_ghost_binding binding = List.exists is_whole_ghost binding.pvb_attributes

let erase =
  object
    inherit Ast_traverse.map as super

    method! attributes attrs =
      super#attributes (List.filter (fun attr -> not (is_ghost attr)) attrs)

    method! structure items =
      List.filter_map
        (fun item ->
          match item.pstr_desc with
          | Pstr_value (_, bindings) when List.exists is_ghost_binding bindings ->
              if List.for_all is_ghost_binding bindings then None
              else
                Location.raise_errorf ~loc:item.pstr_loc
                  "[@@@@ghost] must mark every binding of a `let ... and ...` group"
          | _ -> Some (super#structure_item item))
        items
  end

let expand ~ctxt bound =
  match bound.pexp_desc with
  | Pexp_let (_, _, body) -> body
  | _ ->
      Location.raise_errorf
        ~loc:(Expansion_context.Extension.extension_point_loc ctxt)
        "%%ghost expects a binding: let%%ghost x = e in body"

let ghost_let =
  Extension.V3.declare ghost Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    expand

let () =
  Driver.register_transformation "mica_ghost"
    ~rules:[ Context_free.Rule.extension ghost_let ]
    ~impl:erase#structure;
  Driver.standalone ()
