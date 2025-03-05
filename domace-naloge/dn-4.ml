(*----------------------------------------------------------------------------*
 # 4. domača naloga
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Pri tej nalogi boste napisali svoj simulator Turingovih strojev. Zaradi
 preprostosti bomo za abecedo vzeli kar znake tipa `char`, za prazni znak bomo
 izbrali presledek `' '`, stanja pa bomo predstavili z nizi. Za možne premike
 zafiksiramo tip `direction`:
[*----------------------------------------------------------------------------*)

type direction = Left | Right
type state = string

(*----------------------------------------------------------------------------*
 ## Implementacija trakov
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite modul `Tape`, ki implementira spodnjo signaturo, kjer je:

 - `t` tip v obe smeri neomejenih trakov in glavo na danem mestu;
 - `make`, ki naredi nov trak z znaki iz niza ter glavo na prvem znaku;
 - `print`, ki izpiše vsebino traku (brez presledkov na začetku in koncu) ter
 pod njim z `^` označi mesto glave;
 - `read`, ki vrne znak pod glavo;
 - `write`, ki pod glavo zapiše dani znak;
 - `move`, ki glavo premakne v dano smer.

 Zadnji dve funkciji naj vrneta nov trak, obstoječega pa naj pustita
 nespremenjenega.

 Ker je tip `t` abstrakten, si lahko privoščite poljubno implementacijo, zato
 poskrbite tako za učinkovitost kot za preglednost kode.
[*----------------------------------------------------------------------------*)

module type TAPE = sig
  type t

  val make : string -> t
  val print : t -> unit
  val read : t -> char
  val move : direction -> t -> t
  val write : char -> t -> t
end

module Tape : TAPE = struct
  type t = {
    levi : char list; 
    glava : char ; 
    desni: char list }

  let make niz =
    let znaki = List.init (String.length niz) (String.get niz) in (*list.init (n) (f) naredi sez dolzine n, na i tem mestu pa je elt f(i)*)
    match znaki with
    | [] -> { levi = []; glava = ' '; desni = [] }
    | x :: xs -> { levi = []; glava = x; desni = xs }  
  
  let move smer trak =
    match smer with
    | Right ->
      let nov_levi = trak.glava :: trak.levi in
      let nova_glava = 
        match trak.desni with
        | [] -> ' '
        | x :: xs -> x
      in
      let nov_desni =
        match trak.desni with
        | [] -> []
        | x :: xs -> xs
      in
      {levi = nov_levi; glava = nova_glava; desni = nov_desni}
    | Left ->
      let nov_levi = 
        match trak.levi with
        | [] -> []
        | x :: xs -> xs
      in
      let nova_glava = 
        match trak.levi with
        | [] -> ' '
        | x :: xs -> x
      in
      let nov_desni = trak.glava :: trak.desni in
      {levi = nov_levi; glava = nova_glava; desni = nov_desni}
        

  let read trak = trak.glava

  let write znak trak = 
    {trak with glava = znak}

  let print trak =
    let pravilno_obrnjen_levi_sez = List.rev trak.levi in
    let levi_niz_znakov = String.of_seq (List.to_seq pravilno_obrnjen_levi_sez) in
    let desni_niz_znakov = String.of_seq (List.to_seq trak.desni) in
    let niz_iz_glave = String.make 1 trak.glava in
    let celoten_niz = levi_niz_znakov ^ niz_iz_glave ^ desni_niz_znakov in
    let niz_brez_presledkov = String.trim celoten_niz in
    let glava_pozicija = String.length (String.trim levi_niz_znakov) in
    let kazalec = String.make glava_pozicija ' ' ^ "^" in
    print_endline niz_brez_presledkov;
    print_endline kazalec 
end



let primer_trak = Tape.(
  make "ABCDE"
  |> move Left
  |> move Left
  |> move Right
  |> move Right
  |> move Right
  |> move Right
  |> write '!'
  |> print
)
(*
AB!DE
  ^
*)
(* val primer_trak : unit = () *)

(*----------------------------------------------------------------------------*
 ## Implementacija Turingovih strojev
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite modul `Machine`, ki implementira spodnjo signaturo, kjer je:

 - `t` tip Turingovih strojev;
 - `make`, ki naredi nov stroj z danim začetnim stanjem in seznamom preostalih
 stanj ter prazno prehodno funkcijo;
 - `initial`, ki vrne začetno stanje stroja;
 - `add_transition`, ki prehodno funkcijo razširi s prehodom $(q, a) \mapsto
 (q', a', d)$;
 - `step`, ki za dano stanje in trak izvede en korak stroja, če je to mogoče.

 Zadnji dve funkciji naj vrneta spremenjene vrednosti, obstoječe argumente pa
 naj pustita nespremenjene. Prav tako pri zadnjih dveh funkcijah lahko
 predpostavite, da ju bomo klicali le na poprej podanih stanjih.

 Tudi tu je tip `t` abstrakten, zato poskrbite za učinkovitost in preglednost
 kode.
[*----------------------------------------------------------------------------*)

module type MACHINE = sig
  type t
  val make : state -> state list -> t
  val initial : t -> state
  val add_transition : state -> char -> state -> char -> direction -> t -> t
  val step : t -> state -> Tape.t -> (state * Tape.t) option
end

(*da bom lazje uredila prehodne funkcije*)
module PrehodMap = Map.Make(struct
  type t = state * char
  let compare = compare 
end)

module Machine : MACHINE = struct
  type t = {
    mnozica_simbolov : char list; 
    prazni_znak : char; 
    mnozica_stanj : state list; 
    zacetno_stanje : state; 
    prehodne_funkcije : (state * char * direction) PrehodMap.t;
  }
  
  let make stanje seznam_stanj = 
    { mnozica_simbolov = [];
      prazni_znak = ' ';
      mnozica_stanj = seznam_stanj;
      zacetno_stanje = stanje;
      prehodne_funkcije = PrehodMap.empty;
    }
    
  let initial tur_stroj = tur_stroj.zacetno_stanje

  let add_transition stanje znak novo_stanje nov_znak smer tur_stroj = 
    { tur_stroj with
      prehodne_funkcije = PrehodMap.add (stanje, znak) (novo_stanje, nov_znak, smer) tur_stroj.prehodne_funkcije
    }

  let step tur_stroj stanje trak =
    let znak = Tape.read trak in
    match PrehodMap.find_opt (stanje, znak) tur_stroj.prehodne_funkcije with
    | Some (novo_stanje, nov_znak, smer) -> 
      let nov_trak = trak |> Tape.write nov_znak |> Tape.move smer in
      Some (novo_stanje, nov_trak)
    | None -> None
end
(*----------------------------------------------------------------------------*
 Primer stroja "Binary Increment" na <http://turingmachine.io> lahko
 implementiramo kot:
[*----------------------------------------------------------------------------*)

let binary_increment =
  Machine.(
    make "right" [ "carry"; "done" ]
    |> add_transition "right" '1' "right" '1' Right
    |> add_transition "right" '0' "right" '0' Right
    |> add_transition "right" ' ' "carry" ' ' Left
    |> add_transition "carry" '1' "carry" '0' Left
    |> add_transition "carry" '0' "done" '1' Left
    |> add_transition "carry" ' ' "done" '1' Left
  )

(* val binary_increment : Machine.t = <abstr> *)

(*----------------------------------------------------------------------------*
 Zapišite funkciji `slow_run` in `speed_run` tipa `Machine.t -> str -> unit`, ki
 simulirata Turingov stroj na traku, na katerem je na začetku zapisan dani niz.
 Prva naj izpiše trakove in stanja pri vseh vmesnih korakih, druga pa naj izpiše
 le končni trak. Slednjo bomo uporabljali tudi pri meritvi učinkovitosti
 izvajanja.
[*----------------------------------------------------------------------------*)

let slow_run tur_stroj niz = 
  let zacetni_trak = Tape.make niz in 
  let zacetno_stanje = Machine.initial tur_stroj in 
  let rec pomozna trenutno_stanje trenutni_trak = 
    Tape.print trenutni_trak;
    print_endline trenutno_stanje;
    match Machine.step tur_stroj trenutno_stanje trenutni_trak with
    | Some (stanje, trak) -> 
      pomozna stanje trak
    | None -> ()
  in
  pomozna zacetno_stanje zacetni_trak

let primer_slow_run =
  slow_run binary_increment "1011"
(*
1011
^
right
1011
  ^
right
1011
  ^
right
1011
    ^
right
1011
    ^
right
1011
    ^
carry
1010
  ^
carry
1000
  ^
carry
1100
^
done
*)
(* val primer_slow_run : unit = () *)

let speed_run tur_stroj niz = 
  let zacetni_trak = Tape.make niz in 
  let zacetno_stanje = Machine.initial tur_stroj in 
  let rec pomozna trenutno_stanje trenutni_trak = 
    match Machine.step tur_stroj trenutno_stanje trenutni_trak with
    | Some (stanje, trak) -> pomozna stanje trak
    | None -> Tape.print trenutni_trak
  in
  pomozna zacetno_stanje zacetni_trak

let primer_speed_run =
  speed_run binary_increment "1011"
(*
1100
^
*)
(* val primer_speed_run : unit = () *)

(*----------------------------------------------------------------------------*
 ## Krajši zapis
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Ko definiramo Turingov stroj, prehode običajno združujemo najprej po stanjih,
 nato pa še po znakih. Prav tako pri dosti prehodih samo premikamo glavo, trak
 in stanje pa pustimo pri miru. Zapišite funkcije:

 - `for_state`
 - `for_character`
 - `for_characters`
 - `move`
 - `switch_and_move`
 - `write_and_move`
 - `write_switch_and_move`

 s katerimi bi lahko zgornji primer na krajše zapisali kot spodaj.
 Implementacijo in tipe ugotovite sami.
[*----------------------------------------------------------------------------*)
let for_state stanje sez tur_stroj =
  List.fold_left (fun stroj f -> f stroj stanje) tur_stroj sez

let for_character znak funkcija =
  fun tur_stroj stanje ->
    funkcija tur_stroj stanje znak

let for_characters znaki funkcija =
  fun tur_stroj stanje ->
    List.fold_left (fun stroj znak -> funkcija stroj stanje znak) tur_stroj (List.of_seq (String.to_seq znaki))

let move smer =
  fun tur_stroj stanje znak ->
    Machine.add_transition stanje znak stanje znak smer tur_stroj

let switch_and_move novo_stanje smer =
  fun tur_stroj stanje znak ->
    Machine.add_transition stanje znak novo_stanje znak smer tur_stroj


let write_and_move znak smer =
  fun tur_stroj stanje trenutni_znak ->
    Machine.add_transition stanje trenutni_znak stanje znak smer tur_stroj

let write_switch_and_move znak novo_stanje smer =
  fun tur_stroj stanje trenutni_znak ->
    Machine.add_transition stanje trenutni_znak novo_stanje znak smer tur_stroj


(* let binary_increment' =
  Machine.make "right" ["carry"; "done"]
  |> for_state "right" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ switch_and_move "carry" Left
  ]
  |> for_state "carry" [
    for_character '1' @@ write_and_move '0' Left;
    for_characters "0 " @@ write_switch_and_move '1' "done" Left
  ]   *)
(* val binary_increment' : Machine.t = <abstr> *)

(*----------------------------------------------------------------------------*
 ## Primeri Turingovih strojev
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Pri tej nalogi boste sestavljali stroje, ki bodo iz začetnega niza na traku na
 različne načine izračunali nov niz. Pri tem lahko predpostavite, da je začetni
 niz sestavljen iz ničel in enic, preostanek traku pa je prazen. Na koncu
 izvajanja naj bo glava na začetku novega niza, z izjemo tega niza pa naj bo
 trak prazen. Ni pa treba, da se izračunani niz začne na istem mestu na traku,
 kot se je začel prvotni niz.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ### Obračanje niza
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite Turingov stroj, ki začetni niz obrne na glavo.
[*----------------------------------------------------------------------------*)

let reverse =
  Machine.make "desno" ["levo"; "zapomni_si_1"; "zapomni_si_0"; "brisi_*_"; "spet_isci";  "pojdi_nazaj"; "done"]
  |> for_state "desno" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ switch_and_move "levo" Left
  ]
  |> for_state "levo" [
    for_character '*' @@ move Left;
    for_character '1' @@ write_switch_and_move '*' "zapomni_si_1" Right;
    for_character '0' @@ write_switch_and_move '*' "zapomni_si_0" Right;
    for_character ' ' @@ switch_and_move "brisi_*_" Right
  ]  
  |> for_state "zapomni_si_0" [
    for_characters "01*" @@ move Right;
    for_character ' ' @@ write_switch_and_move '0' "spet_isci" Left
  ]  
  |> for_state "zapomni_si_1" [
    for_characters "01*" @@ move Right;
    for_character ' ' @@ write_switch_and_move '1' "spet_isci" Left
  ]  
  |> for_state "spet_isci" [
    for_characters "01" @@ move Left;
    for_character '*' @@ switch_and_move "levo" Left;
    for_character ' ' @@ switch_and_move "done" Right
  ] 
  |> for_state "brisi_*_" [
    for_characters "01" @@ switch_and_move "pojdi_nazaj" Left;
    for_character '*' @@ write_and_move ' ' Right;
    for_character ' ' @@ switch_and_move "done" Right
  ] 
  |> for_state "pojdi_nazaj" [
    for_character ' ' @@ switch_and_move "done" Right
  ] 

let primer_reverse = speed_run reverse "0000111001"
(* 
1001110000          
^
*)
(* val primer_reverse : unit = () *)

(*----------------------------------------------------------------------------*
 ### Podvajanje niza
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite Turingov stroj, ki podvoji začetni niz.
[*----------------------------------------------------------------------------*)

let duplicate =
  Machine.make "zacni" ["poisci_prazno_mesto"; "pojdi_na_zacetek"; "desno"; "zapomni_si_0"; "zapomni_si_1";  "podvoji_0"; "podvoji_1"; "done"]
  |> for_state "zacni" [
    for_characters "01" @@ switch_and_move "poisci_prazno_mesto" Right;
    for_character ' ' @@ switch_and_move "done" Right
  ]
  |> for_state "poisci_prazno_mesto" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ write_switch_and_move '*' "pojdi_na_zacetek" Left
  ]  
  |> for_state "pojdi_na_zacetek" [
    for_characters "01*" @@ move Left;
    for_character ' ' @@ switch_and_move "desno" Right
  ] 
  |> for_state "desno" [
    for_character '0' @@ write_switch_and_move ' ' "zapomni_si_0" Right;
    for_character '1' @@ write_switch_and_move ' ' "zapomni_si_1" Right;
    for_character '*' @@ write_switch_and_move ' ' "done" Right
  ] 
  |> for_state "zapomni_si_0" [
    for_characters "01*" @@ move Right;
    for_character ' ' @@ write_switch_and_move '0' "podvoji_0" Right
  ]  
  |> for_state "zapomni_si_1" [
    for_characters "01*" @@ move Right;
    for_character ' ' @@ write_switch_and_move '1' "podvoji_1" Right
  ]  
  |> for_state "podvoji_0" [
    for_character ' ' @@ write_switch_and_move '0' "pojdi_na_zacetek" Left
  ] 
  |> for_state "podvoji_1" [
    for_character ' ' @@ write_switch_and_move '1' "pojdi_na_zacetek" Left
  ] 

let primer_duplicate = speed_run duplicate "010011"
(* 
001100001111       
^
*)
(* val primer_duplicate : unit = () *)

(*----------------------------------------------------------------------------*
 ### Eniški zapis
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite Turingov stroj, ki na začetku na traku sprejme število $n$, zapisano
 v dvojiškem zapisu, na koncu pa naj bo na traku zapisanih natanko $n$ enic.
[*----------------------------------------------------------------------------*)

let to_unary =
  Machine.make "zacni" ["isci_prazno"; "nazaj_do_prve"; "preberi_prvo";
  "postopek_za_0"; "postopek_za_1"; "spremeni_1_v_a_za_0"; "spremeni_1_v_a_za_1"; "preberi_a"; "dodaj_novo_1";
  "done"]
  (*algoritem po vrsti bere in dela nov niz desno od zacetnega, 
  ce prebere 1ko, nov niz podvoji in doda še eno enko, ce prebere 0, pa niz samo podvoji*)
  |> for_state "zacni" [
    for_characters "01" @@ switch_and_move "isci_prazno" Right;
    for_character ' ' @@ switch_and_move "done" Right
  ]
  |> for_state "isci_prazno" [
    for_characters "01" @@ move Right;
    for_character ' ' @@ write_switch_and_move '*' "nazaj_do_prve" Left
  ]
  |> for_state "nazaj_do_prve" [
    for_characters "01a*" @@ move Left;
    for_character ' ' @@ switch_and_move "preberi_prvo" Right
  ]
  |> for_state "preberi_prvo" [
    for_character '0' @@ write_switch_and_move ' ' "postopek_za_0" Right;
    for_character '1' @@ write_switch_and_move ' ' "postopek_za_1" Right;
    for_character '*' @@ write_switch_and_move ' ' "done" Right
  ]
  |> for_state "postopek_za_0" [
    for_characters "01" @@ move Right;
    for_character '*' @@ switch_and_move "spremeni_1_v_a_za_0" Right
  ]
  |> for_state "postopek_za_1" [
    for_characters "01" @@ move Right;
    for_character '*' @@ switch_and_move "spremeni_1_v_a_za_1" Right
  ]
  |> for_state "spremeni_1_v_a_za_0" [
    for_character '1' @@ write_and_move 'a' Right;
    for_character ' ' @@ switch_and_move "preberi_a" Left
  ]
  |> for_state "spremeni_1_v_a_za_1" [
    for_character '1' @@ write_and_move 'a' Right;
    for_character ' ' @@ write_switch_and_move '1' "preberi_a" Left
  ]
  |> for_state "preberi_a" [
    for_character 'a' @@ write_switch_and_move '1' "dodaj_novo_1" Right;
    for_character '1' @@ move Left;
    for_character '*' @@ switch_and_move "nazaj_do_prve" Left
  ]
  |> for_state "dodaj_novo_1" [
    for_character ' ' @@ write_switch_and_move '1' "preberi_a" Left;
    for_characters "a1" @@ move Right
  ]

let primer_to_unary = speed_run to_unary "1010"
(* 
1111111111
^
*)
(* val primer_to_unary : unit = () *)

(*----------------------------------------------------------------------------*
 ### Dvojiški zapis
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite ravno obratni Turingov stroj, torej tak, ki na začetku na traku
 sprejme število $n$ enic, na koncu pa naj bo na traku zapisano število $n$ v
 dvojiškem zapisu.
[*----------------------------------------------------------------------------*)

let to_binary = 
  Machine.make "zacni" ["spremeni_v_a"; "izbrisi_zadnji_a"; "pojdi_na_zacetek";
  "pristej_a"; "poisci_zadnji_a"; "namesto_praznega_niza_vrni_0"; "done"]
  (*stroj sesteva enke, ampak da ne bo tezav, na zacetku enke spremeni v a-je. 
  Nov niz pise levo od zacetnega; a-je sproti brise in binarnemu zapisu pristeva 1*)
  |> for_state "zacni" [
    for_characters "01" @@ write_switch_and_move 'a' "spremeni_v_a" Right;
    for_character ' ' @@ write_switch_and_move '0' "namesto_praznega_niza_vrni_0" Right  
  ]
  |> for_state "spremeni_v_a" [
    for_characters "01" @@ write_and_move 'a' Right;
    for_character ' ' @@ switch_and_move "izbrisi_zadnji_a" Left
  ]
  |> for_state "izbrisi_zadnji_a" [
    for_character 'a' @@ write_switch_and_move ' ' "pristej_a" Left;
    for_characters "01" @@ switch_and_move "pojdi_na_zacetek" Left
  ]
  |> for_state "pojdi_na_zacetek" [
    for_characters "01" @@ move Left;
    for_character ' ' @@ switch_and_move "done" Right
  ]
  |> for_state "pristej_a" [
    for_character 'a' @@ move Left;
    for_characters "0 " @@ write_switch_and_move '1' "poisci_zadnji_a" Right;
    for_character '1' @@ write_and_move '0' Left
  ]
  |> for_state "poisci_zadnji_a" [
    for_characters "01a" @@ move Right;
    for_character ' ' @@ switch_and_move "izbrisi_zadnji_a" Left
  ]
  |> for_state "namesto_praznega_niza_vrni_0" [
    for_character ' ' @@ switch_and_move "done" Left
  ]

let primer_to_binary = speed_run to_binary (String.make 42 '1')
(* 
101010                                           
^
*)
(* val primer_to_binary : unit = () *)
