open MiscTools

type moduleChunk
  = McOpen       of moduleItem ref
  | McRename     of bool * string * moduleItem ref
  | McInclude    of bool * moduleItem ref
  | McDefinition of string(* signature_item_desc list *)
  | McComment    of string
and moduleItem
  = { mi_chunks : moduleChunk list
    ; mi_parent : (moduleItem ref) option
    ; mi_oname  : string
    ; mi_nname  : string list
    }
let addRawChunks self chunks =
  self := { !self with mi_chunks = !self.mi_chunks @ chunks }
let isMcOpen x
  = match x with McOpen _ -> true | _ -> false 
let isMcRename x
  = match x with McRename _ -> true | _ -> false
let isMcInclude x
  = match x with McInclude _ -> true | _ -> false
let isMcDefinition x
  = match x with McDefinition _ -> true | _ -> false

let createdModules: moduleItem ref list ref = ref []
let registerModule (m: moduleItem ref) = 
    createdModules := m :: !createdModules; ()
let emptyModule (oname: string) (parent: moduleItem ref option)
  : moduleItem ref
  = let newModule =
      ref { mi_chunks = []
        ; mi_parent = parent
        ; mi_oname  = oname
        ; mi_nname  = (match parent with
                       | Some p -> (@) !p.mi_nname
                       | None   -> id) [oname]
        }
    in registerModule newModule;
       newModule

let patchDefinition x =
  replace "| LScons of coq_Z option * stmt * lbl_stmt" "| LScons of coq_Z option * stmt * unit" x
  
let chunkToString (c: moduleChunk)
  = match c with
  | McOpen m -> protect ( "open " ^ ldot !m.mi_nname)
  | McRename (_, a, m) -> protect ( "module " ^ a ^ " = " ^ ldot !m.mi_nname)
  | McInclude (_, m) -> protect ( "include " ^ ldot !m.mi_nname)
  | McDefinition s -> patchDefinition s (* prettyPrintDefinition s *)
  | McComment s -> protect ("(* " ^ s ^ " *)")
                 
let generateDummyType =
  let _id = ref 0 in
  (fun () ->
    _id := !_id + 1;
    let id = string_of_int !_id in
    "open Prims\ntype dummyType" ^ id ^ " = | DummyType"^ id ^ "\nval dummyVal" ^ id ^ " : int" )
                 
let moduleItemToString (m: moduleItem) =
  let more =
    if ldot m.mi_nname = "DoubleUnderscore" then
      []
    else
      ["open DoubleUnderscore"; "open FStar.Char"]
  in
  protect ("module " ^ ldot m.mi_nname) ^ "\n" ^ (String.concat "\n" more) ^ "\n" ^ generateDummyType () ^ "\n\n"
  ^ (List.fold_left (fun acc c -> acc ^ "\n" ^ c) ""
       (List.map chunkToString m.mi_chunks)) ^ "\n\nopen Prims"
 

let getNewId =
  let _uid = ref 0 in
  (fun () -> _uid := !_uid + 1; !_uid)
  
let externalizeChunksInSelf (self: moduleItem ref)
  : moduleItem ref * moduleChunk list
  = let myId = getNewId () in
    let oname = "Chunk" ^ padding (string_of_int myId) 5 in
    (* let oname = (!self).mi_oname ^ "_chunk_" ^ string_of_int myId in *)
    let op  = (!self).mi_chunks in
    let op' = List.filter (not << isMcDefinition) op in
    let sub
      = ref { mi_chunks = op
            ; mi_parent = Some self
            ; mi_oname  = oname
            ; mi_nname  = !self.mi_nname @ [oname]
          };
    in
    self := { !self with
              mi_chunks = op @ [ McInclude (false, sub) ]
            };
    registerModule sub;
    (sub, op')
