open Format
open Parsetree
open Location
open Lexing
open MFCore
open MiscTools
   
let global_basedir = "/tmp/chose/"
let global_outdir  = "/tmp/output_fsti/"
let () =
  Sys.command ("rm -rf " ^ global_outdir);
  Sys.command ("mkdir " ^ global_outdir);
  ()

let file_modules: string list =
  let isMLI x = Filename.extension x = ".mli" in
  let l = Array.to_list (Sys.readdir global_basedir) in
  List.map Filename.chop_extension (List.filter isMLI l)

   
let writeModuleItem (m: moduleItem)
  = let body = moduleItemToString m in
    let oc = open_out (global_outdir ^ ldot m.mi_nname ^ ".fsti") in
    Printf.fprintf oc "%s" body;
    close_out oc
  
let writeCreatedModules () =
  let doubleUnderscore = emptyModule "DoubleUnderscore" None in
  let addTypesTo dest = List.iter (fun t -> addRawChunks dest
                        [McDefinition ("type "^t)]) in
  addTypesTo doubleUnderscore
    [ "float32"    ; "float64"
    ; "float"      ; "'a top_op"
    ; "'a leb_op"  ; "('a, 'b) join_op"
    ; "'a botlift" ; "'a toplift"
    ; "coq_val"    ; "block"
    ; "__"         ; "trivialMulDiscr"
    ; "mreg"       ; "loc"
    ];
  let zarith = emptyModule "FastArithImpl.ZArith" None in
  addTypesTo zarith ["t"];
  List.iter (fun mr ->
      printf "%s\n" ("Printing " ^ ldot !mr.mi_nname);
      writeModuleItem !mr
    ) !createdModules

  
let makeSubModuleSig (sur: moduleItem ref) (sign: signature) =
  let rec h sign
    = match sign with
    | [] -> []
    | _ -> []
  in ()
let makeSubModule (sur: moduleItem ref) (sup: module_declaration)
  = match sup.pmd_type.pmty_desc with
  | Pmty_signature sign -> makeSubModuleSig sur sign
  | _ -> ()

let dummy_loc = {loc_start = Lexing.dummy_pos; loc_end = Lexing.dummy_pos; loc_ghost = false}
let sid_to_si desc: signature_item = {psig_desc=desc; psig_loc = dummy_loc} 


  
let locationRecoverOriginalString l =
  let filename = l.loc_start.pos_fname in
  let line_start = l.loc_start.pos_lnum in
  let line_end = l.loc_end.pos_lnum in
  let lines = line_end - line_start + 1 in
  let rec h nth =
    if nth <= line_end then
      (if nth = line_start then "" else "\n") ^ nth_line nth filename ^ h (nth + 1)
    else
      ""
  in
  String.trim (h line_start)

let module_with_add_stuff sub parentName =
  let defs =
    match parentName with
    | "TYPE_EQ" -> ["type t"; "type s"] 
    | "SHARETREE" -> ["type 'x t"; "type elt"] 
    | "SET" -> ["type t"; "type elt"]
    | _ -> []
  in addRawChunks sub [McDefinition (String.concat "\n" defs)];
     ()
  
let rec addChunkToModule (filename: string) (self: moduleItem ref) (si: signature_item) =
  let addComment str =
    printf "\n\n #### %s \n\n" str;
    addRawChunks self [McComment str]
  in
  let addAString str = addRawChunks self [McDefinition str] in
  let getStringOf sid = locationRecoverOriginalString sid.psig_loc in
  let addAsString (sid: signature_item) =
    addAString (getStringOf sid)
  in
  let si_desc = si.psig_desc in
  match si_desc with
  | Psig_open odesc ->
     (* here, either:
        - odesc refers to a file module, then we take the first chunk in path, and we generate "modules X = Y"s, then we go again
        - odesc refers to a module accessible through some other open module. In that case, we juste look for a previous module statement in self
      *)
     let lId = Longident.flatten odesc.popen_lid.txt in
     let sId = String.concat "." lId in
     let hId = List.hd lId in
     let rec resolve_explicit_module m: unit =
       let chunks = resolve_explicit_module' true m in
       addRawChunks self [McOpen m];
       addRawChunks self chunks
     and resolve_explicit_module' (filter: bool) m: moduleChunk list =
       let f_filter chunk
         = match chunk with
         | McRename  (p, _, _) -> not filter || p
         | McInclude (p, _) -> not filter || p
         | _ -> false
       in
       let f_map chunk
         = match chunk with
         | McRename  (_, a, b) -> [McRename (false, a, b)]
         | McInclude (_, a)    -> (McInclude (false, a)) :: (resolve_explicit_module' false a)
       in
       List.concat (List.map f_map
             (List.filter f_filter !m.mi_chunks))
     in
     let resolve_file () =
       match List.find_opt ((=) hId) file_modules with
       | Some mn -> (match List.find_opt (fun x -> hId = !x.mi_oname) !createdModules with
                     | Some readyMod -> resolve_explicit_module readyMod
                     | None -> (* the module is not loaded yet, let's do so *)
                        let m = loadModuleFromFile mn in
                        resolve_explicit_module m
                    )
       | None    -> ()
     in
     let resolve_accessible ()
       = let d = List.find_opt
                 (fun (McRename (p, n, _)) -> n = sId)
                 (List.filter isMcRename !self.mi_chunks)
         in match d with
            | Some (McRename (_, _, m)) -> 
               resolve_explicit_module m
            | None   -> resolve_file ()
     in
     resolve_accessible ()
  | Psig_module mdecl ->
     ( match mdecl.pmd_type.pmty_desc with
       | Pmty_signature body -> 
          let previousStuff, op = externalizeChunksInSelf self in
          let subName = mdecl.pmd_name.txt in
          let sub = emptyModule subName (Some self) in
          addRawChunks sub op;
          addRawChunks self [McRename (true, subName, sub)];
          addSignatureToModule filename sub body;
          (* addRawChunks *) ()
       | Pmty_with (_, _) ->
          let previousStuff, op = externalizeChunksInSelf self in
          let subName = mdecl.pmd_name.txt in
          let sub = emptyModule subName (Some self) in
          (* addRawChunks sub op; *)
          addRawChunks self [McRename (true, subName, sub)];
          let raw = getStringOf si in
          Str.search_forward (Str.regexp "^ +\\([^= ]+\\) with") raw 0;
          let parentName = String.trim (Str.matched_group 1 raw) in
          printf "\nPARENT_NAME seen: %s\n" parentName;
          let re = Str.regexp "with +\\(type +[^=]+\\)" in
          let rec loop position =
            try
              let position = Str.search_forward re raw position in
              let str = Str.matched_group 1 raw in
              str :: (loop (position + 1))
            with _ -> []
          in
          (* addRawChunks sub [McDefinition (String.concat "\n" (loop 0))]; *)
          module_with_add_stuff sub parentName;
          addRawChunks self [McRename (true, subName, sub)];
          ()
          (* addSignatureToModule filename sub body; *)
          (* addComment ("PMTY//"^mdecl.pmd_name.txt); () *)
       | _ -> ()
          (* addComment ("PMTY//"^mdecl.pmd_name.txt); () *)
     )
  | Psig_modtype _ -> addComment "Warning: here, we had a _modtype_, we lost it."
  | Psig_recmodule _ -> addComment "Warning: here, we had a _recmodule_, we lost it."
  | _ ->
     let raw = String.trim (getStringOf si) in
     let typesToHide = [
         "ab_machine_env"
       ; "ab_ideal_env"
       ; "ab_ideal_nonrel"
       ; "ab_ideal_env_nochan"
       ; "mem_dom"
       ; "coq_R_union"
       ; "coq_R_diff"
       ; "coq_R_inter"
       ; "query_chan"] in
     let rec loopHide list = match list with
       | [] -> raw
       | hd::tl ->
          let hd = Str.quote hd in
          let re = Str.regexp ("\\(type [^=]*" ^ hd ^ "\\) *=") in
          if Str.string_match re raw 0
          then Str.matched_group 1 raw
          else loopHide tl
     in
     let raw = loopHide typesToHide in
     let valToRemove = ["assume"; "default"] in
     let rec loopRm list = match list with
       | [] -> Some raw
       | hd::tl ->
          let hd = Str.quote hd in
          let re = Str.regexp ("val +"^ hd ^ "\\b") in
          if Str.string_match re raw 0
          then None
          else loopRm tl
     in
     match loopRm valToRemove with
     | Some raw ->
        let x = "[a-zA-Z_.0-9\t\n ]+\\b *" in
        let x = String.concat "\\*" [x;x;x;x;x;x;x;x;x;x;x;x;x] in
        let raw = Str.global_replace
                    (Str.regexp ("\\(" ^ x ^ "\\)\\*"))
                    "(\\1) * "
                    raw in
        let raw = Str.global_replace
                    (Str.regexp ("\bassume\b"))
                    "assume_"
                    raw in
        let raw = Str.global_replace
                    (Str.regexp ("\bdefault\b"))
                    "default_"
                    raw in
        addAString raw
     | None -> ()
     
and addSignatureToModule filename (self: moduleItem ref) (s: signature): unit
  = List.iter (fun i -> addChunkToModule filename self i) s
and loadModuleFromFile  (mn: string): moduleItem ref
  = printf "%s" ("loadModuleFromFile: " ^ mn ^ "\n");
  match List.find_opt (fun x -> mn = !x.mi_oname) !createdModules with
  | Some readyMod -> readyMod
  | None -> 
     let fn = global_basedir ^ mn ^ ".mli" in
     let r = Pparse.parse_interface ~tool_name:"ocamlc" Format.err_formatter fn in
     let self = emptyModule mn None in
     addSignatureToModule fn self r;
     self
let newDummyHasEqName =
  let _id = ref 0 in
  let f () = _id:=!_id + 1; "dummyHasEq"^string_of_int !_id in
  f
let signatureToFile (tree: signature) fileout =
  (* let b = Buffer.create 1000 in *)
  let f = Format.formatter_of_out_channel fileout in
  Customprint.signature f tree;
  Format.pp_print_flush f
let rearrangeOutput () =
  let f fn
    = let ff = global_outdir ^ fn in
      let r  = Pparse.parse_interface ~tool_name:"ocamlc" Format.err_formatter ff in
      (* Sys.command ("rm -f " ^ ff); *)
      let oc = open_out ff in
      let s = signatureToFile r oc in
      close_out oc
  in
  let f2 fn =
    let ff = global_outdir ^ fn in
    let lines = read_lines ff in
    let re = Str.regexp "val ppp\\([0-9]+\\) : int" in
    let lines = List.map (fun line ->
                    let l = String.trim line in
                    if Str.string_match re l 0
                    then let i = Str.matched_group 1 l in
                         (* printf "\ni was %s\n" i; *)
                         List.nth !protected_strings (int_of_string i) ^ "(* recovered *)"
                    else (
                      let re = Str.regexp "^type +\\([^=]+\\)$" in
                      if Str.string_match re l 0
                      then let i: string = Str.matched_group 0 l in
                           let k: string = Str.matched_group 1 l in
                             "assume new "
                           ^ i
                           ^ "\nval "
                           ^ newDummyHasEqName ()
                           ^ ": hasEq ("^k^") \n"
                      else
                        line
                    )
                  ) lines in
    (* Sys.command ("rm -f " ^ ff); *)
    let oc = open_out ff in
    Printf.fprintf oc "%s" (String.concat "\n" lines);
    close_out oc
  in
  let isFSTI x = Filename.extension x = ".fsti" in
  let l = Array.to_list (Sys.readdir global_outdir) in
  let l = (List.filter isFSTI l) in
  List.iter f l;
  List.iter f2 l

(* let () =
 *      let raw = "type query_chan =\nasdsd" in
 *      let typesToHide = ["ab_machine_env"; "ab_ideal_env_nochan"; "mem_dom"; "ab_ideal_nonrel"; "query_chan"] in
 *      let rec loopHide list = match list with
 *        | [] -> raw
 *        | hd::tl ->
 *           let hd = Str.quote hd in
 *           printf "\n\nREGEX= %s" ("\\(type [^=]*" ^ hd ^ "\\) *=");
 *           let re = Str.regexp ("\\(type [^=]*" ^ hd ^ "\\) *=") in
 *           if Str.string_match re raw 0
 *           then Str.matched_group 1 raw
 *           else loopHide tl
 *      in
 *      let raw = loopHide typesToHide in
 *      if Str.string_match (Str.regexp_string "val assume") raw 0
 *      then ()
 *      else
 *        printf "%s" raw *)
       
  
let () =
  (* let all = List.map show_module ["Integers"] (\*file_modules*\) in *)
  printf "## Begin\n";
  List.iter (fun x -> loadModuleFromFile x; ()) file_modules;
  (* loadModuleFromFile "Integers"; *)
  writeCreatedModules ();
  printf "## End\n";
  (* read_line (); *)
  rearrangeOutput ();
  ()
    
(* let () =
 *   let re = Str.regexp "^txxxype +([^ =]+)[^=]*$" in
 *    let x = List.map (fun line ->
 *                     let l = String.trim line in
 *                     if Str.string_match re l 0
 *                     then let i = Str.matched_group 1 l in
 *                          (\* printf "\ni was %s\n" i; *\)
 *                          List.nth !protected_strings (int_of_string i) ^ "(\* recovered *\)"
 *                     else ( (\* TODO: turn every "type nalme p1 .. pn" into "assume ..." *\)
 *                       let re = Str.regexp "^type +\([^ =]+\)[^=]*$" in
 *                       if Str.string_match re l 0
 *                       then let i: string = Str.matched_group 0 l in
 *                            let k: string = Str.matched_group 1 l in
 *                              "assume new "
 *                            ^ i
 *                            ^ "\nval "
 *                            ^ newDummyHasEqName ()
 *                            ^ ": hasEq "^k^" \n"
 *                       else
 *                         line
 *                     )
 *      ) [
 *        "type hey"
 *              ] in
 *    printf "%s" (String.concat "\n" x);
 *    () *)
