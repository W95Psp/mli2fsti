let (<<) f g x = f(g(x))
let id x = x
let ldot = String.concat "."

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let read_lines name : string list =
  let ic = open_in name in
  let try_read () =
    try Some (input_line ic) with End_of_file -> None in
  let rec loop acc = match try_read () with
    | Some s -> loop (s :: acc)
    | None -> close_in ic; List.rev acc in
  loop []
let replace input output =
  Str.global_replace (Str.regexp_string input) output
let protected_strings: string list ref = ref []
let protect (s: string) =
  protected_strings := !protected_strings @ [s];
  "val ppp" ^ string_of_int (List.length !protected_strings - 1) ^ ":int" ^ "(*" ^ s ^ "*)"

let padding s n =
  let l = String.length s in
  (if l < n
   then String.make (n - l) '0'
   else "") ^ s

                
let input_line_opt ic =
  try Some (input_line ic)
  with End_of_file -> None
 
let nth_line n filename =
  let ic = open_in filename in
  let rec aux i =
    match input_line_opt ic with
    | Some line ->
        if i = n then begin
          close_in ic;
          (line)
        end else aux (succ i)
    | None ->
        close_in ic;
        failwith "end of file reached"
  in
  aux 1
    
