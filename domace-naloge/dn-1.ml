(* # 1. domača naloga *)

(* ## Ogrevanje **************************************************************************************)

(** Števke *)
let stevke b n = 
   let rec stevke_pomozna b n sez =
     match n with
     | 0 -> sez
     | _ -> stevke_pomozna b (n / b) ((n mod b)::sez)
   in stevke_pomozna b n []
(* let primer_1_1 = stevke 10 12345 *)
(* let primer_1_2 = stevke 2 42 *)
(* let primer_1_3 = stevke 16 ((3 * 16 * 16 * 16) + (14 * 16 * 16) + (15 * 16) + 9) *)

(** Začetek seznama *)
let take n sez =
   let rec take_pomozna n sez nov =
     match sez, n with
       | [], _ -> List.rev nov
       | _, 0 -> List.rev nov
       | x::xs, n when n >= List.length sez -> sez
       | x::xs, _ ->  take_pomozna (n - 1) xs (x :: nov)
   in
   take_pomozna n sez []
(* let primer_1_4 = take 3 [ 1; 2; 3; 4; 5 ] *)
(* let primer_1_5 = take 10 [ 1; 2; 3; 4; 5 ] *)

(** Odstranjevanje ujemajočih *)
let rec drop_while f sez =
   match sez with
       | [] -> []
       | x::xs -> if f x then drop_while f xs else sez
(* let primer_1_6 = drop_while (fun x -> x < 5) [ 3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5 ] *)
(* let primer_1_7 = drop_while (fun x -> x < 5) [ 9; 8; 7; 6; 5; 4; 3; 2; 1; 0 ] *)

(** Funkcija `filter_mapi` *)


let filter_mapi f sez =
   let rec filter_mapi_pomozna f sez i nov =
     match sez with
       | [] -> List.rev nov
       | x::xs -> 
         match f i x with 
         | Some rezultat -> filter_mapi_pomozna f xs (i + 1) (rezultat :: nov) 
         | None -> filter_mapi_pomozna f xs (i + 1) nov
   in
   filter_mapi_pomozna f sez 0 []

(* let primer_1_8 =
   filter_mapi
     (fun i x -> if i mod 2 = 0 then Some (x * x) else None)
     [ 1; 2; 3; 4; 5; 6; 7; 8; 9 ] *)


(* ## Izomorfizmi množic **********************************************************************************************)

type ('a, 'b) sum = In1 of 'a | In2 of 'b

(** $A \times B \cong B \times A$ *)

let phi1 (a, b) =
   (b, a)
let psi1 (b, a) =
   (a, b)


(** $A + B \cong B + A$ *)
let phi2 =
   function
   | In1 a -> In2 a
   | In2 b -> In1 b
 
let psi2 =
   function
   | In1 b -> In2 b
   | In2 a -> In1 a

(** $A \times (B \times C) \cong (A \times B) \times C$ *)

let phi3 (a, (b, c)) =
   (a, b), c
 
let psi3 ((a, b), c) =
   a, (b, c)

(** $A + (B + C) \cong (A + B) + C$ *)

let phi4  =
  function
  | In1 a -> In1 (In1 a)
  | In2 (In1 b) -> In1 (In2 b)
  | In2 (In2 c) -> In2 c

let psi4  =
  function
  | In1 (In1 a) -> In1 a
  | In1 (In2 b) -> In2 (In1 b)
  | In2 c -> In2 (In2 c)

(** $A \times (B + C) \cong (A \times B) + (A \times C)$ *)


let phi5 (a, vsota) =
   match vsota with
   | In1 b -> In1 (a, b)
   | In2 c -> In2 (a, c)
 
let psi5 =
   function
   | In1 (a, b) -> (a, In1 b)
   | In2 (a, c) -> (a, In2 c)
   
(** $A^{B + C} \cong A^B \times A^C$ *)

let phi6 f = (fun b -> f (In1 b), fun c -> f (In2 c))

let psi6 (f, g) vsota_b_in_c = 
  match vsota_b_in_c with
  | In1 a -> f a 
  | In2 b -> g b

(** $(A \times B)^C \cong A^C \times B^C$ *)

let phi7 f = ((fun c -> fst (f c)), (fun c-> snd (f c)))
let psi7 (f, g) = fun a -> (f a, g a)


(* ## Polinomi ****************************************************************************************** *)

type polinom = int list

(** Odstranjevanje odvečnih ničel *)


let rec pocisti sez : polinom = 
  match List.rev sez with
    | [] -> sez
    | x :: xs when x = 0 -> pocisti (List.rev xs)
    | _ -> sez

(* let primer_3_1 = pocisti [ 1; -2; 3; 0; 0 ] *)

(** Seštevanje *)

let rec ( +++ ) polinom1 polinom2 : polinom =
  match polinom1, polinom2 with
  | [], [] -> []
  | [], _ -> pocisti polinom2
  | _, [] -> pocisti polinom1
  | x :: xs, y :: ys -> (x + y) :: pocisti (xs +++ ys)
(* let primer_3_2 = [ 1; -2; 3 ] +++ [ 1; 2 ] *)
(* let primer_3_3 = [ 1; -2; 3 ] +++ [ 1; 2; -3 ] *)

(** Množenje *)

let rec ( *** ) (polinom1: polinom) (polinom2: polinom) : polinom = 
  match polinom1, polinom2 with
  | [], [] -> []
  | _, [] -> []
  | [], _ -> []
  | x :: xs, y :: ys-> (x * y) :: pocisti (([x] *** ys ) +++ (xs *** polinom2))

(* let primer_3_4 = [ 1; 1 ] *** [ 1; 1 ] *** [ 1; 1 ] *)
(* let primer_3_5 = [ 1; 1 ] *** [ 1; -1 ] *)

(** Izračun vrednosti v točki *)


let vrednost polinom tocka =
   let rec vrednost_pomozna polinom tocka indeks =
     let rec potenca st pot =
       match pot with
       | 0 -> 1
       | _ -> st * potenca st (pot - 1)
     in 
     match polinom with
     | [] -> 0
     | x :: xs -> (x * potenca tocka indeks) + vrednost_pomozna xs tocka (indeks + 1)
 in
 vrednost_pomozna polinom tocka 0
 
(* let primer_3_6 = vrednost [ 1; -2; 3 ] 2 *)

(** Odvajanje *)

let odvod (polinom: polinom) : polinom  =
  let rec odvod_pomozna polinom indeks = 
    match polinom, indeks with
    | [], _ -> []
    | x :: xs, 0 -> odvod_pomozna xs (indeks + 1)
    | x :: xs, _ -> (x * indeks) :: odvod_pomozna xs (indeks + 1)
  in
  odvod_pomozna (pocisti polinom) 0
(* let primer_3_7 = odvod [ 1; -2; 3 ] *)

(** Lep izpis *)
let izpis (polinom: polinom) =
  let stevilo_v_potenco n =
    let rec pretvori_zadnjo_stevko stevilo nov =
      if stevilo = 0 then
        nov
      else
        let zadnja_stevka = stevilo mod 10 in
        let potenca_niz =
          match zadnja_stevka with
          | 0 -> "⁰"
          | 1 -> "¹"
          | 2 -> "²"
          | 3 -> "³"
          | 4 -> "⁴"
          | 5 -> "⁵"
          | 6 -> "⁶"
          | 7 -> "⁷"
          | 8 -> "⁸"
          | 9 -> "⁹"
          | _ -> "" 
        in
        pretvori_zadnjo_stevko (stevilo / 10) (potenca_niz ^ nov) 
    in pretvori_zadnjo_stevko n ""
  in
      
  let rec pomozna_z_indeksi okrajsan_polinom indeks nov =
    match okrajsan_polinom, indeks with

    | [], _ -> nov

    | x :: xs, 0 when x > 0 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ((Int.to_string x) ^ nov)
    | x :: xs, 0 when x > 0 -> pomozna_z_indeksi xs (indeks + 1) (" + " ^ (Int.to_string x) ^ nov)
    | x :: xs, 0 when x < 0 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ((Int.to_string x) ^ nov)
    | x :: xs, 0 when x < 0 -> pomozna_z_indeksi xs (indeks + 1) (" - " ^ (String.make 1 (String.get (Int.to_string x) 1)) ^ nov)
    | x :: xs, 0 when x = 0 -> pomozna_z_indeksi xs (indeks + 1) nov

    | x :: xs, 1 when x = 1 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ("x" ^ nov)
    | x :: xs, 1 when x = 1 -> pomozna_z_indeksi xs (indeks + 1) (" + x" ^ nov)
    | x :: xs, 1 when x > 1 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ((Int.to_string x) ^ " x" ^ nov)
    | x :: xs, 1 when x > 1 -> pomozna_z_indeksi xs (indeks + 1) (" + " ^ (Int.to_string x) ^ " x" ^ nov)
    | x :: xs, 1 when x > 1 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ((Int.to_string x) ^ " x" ^ nov)
    | x :: xs, 1 when x = -1 -> pomozna_z_indeksi xs (indeks + 1) (" - x " ^ nov)
    | x :: xs, 1 when x < -1 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ("- x " ^ nov)
    | x :: xs, 1 when x < -1 -> pomozna_z_indeksi xs (indeks + 1) (" - " ^ (String.make 1 (String.get (Int.to_string x) 1)) ^ " x" ^ nov)
    | x :: xs, 1 when x = 0 -> pomozna_z_indeksi xs (indeks + 1) nov

    | x :: xs, _ when x = 1 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ("x" ^ (stevilo_v_potenco indeks) ^ nov)
    | x :: xs, _ when x = 1 -> pomozna_z_indeksi xs (indeks + 1) (" + x" ^ (stevilo_v_potenco indeks) ^ nov)
    | x :: xs, _ when x > 1 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ((Int.to_string x) ^ " x" ^ (stevilo_v_potenco indeks) ^ nov)
    | x :: xs, _ when x > 1 -> pomozna_z_indeksi xs (indeks + 1) (" + " ^ (Int.to_string x) ^ " x" ^ (stevilo_v_potenco indeks) ^ nov)
    | x :: xs, _ when x = -1 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ("-x" ^ (stevilo_v_potenco indeks) ^ nov)  
    | x :: xs, _ when x = -1 -> pomozna_z_indeksi xs (indeks + 1) (" - x" ^ (stevilo_v_potenco indeks) ^ nov)
    | x :: xs, _ when x < -1 && List.length xs = 0 -> pomozna_z_indeksi xs (indeks + 1) ((Int.to_string x) ^ " x" ^ (stevilo_v_potenco indeks) ^ nov)
    | x :: xs, _ when x < -1 -> pomozna_z_indeksi xs (indeks + 1) (" - " ^ (String.make 1 (String.get (Int.to_string x) 1)) ^ " x" ^ (stevilo_v_potenco indeks) ^ nov)
    | x :: xs, _ when x = 0 -> pomozna_z_indeksi xs (indeks + 1) nov

    | _, _ -> failwith ""

  in pomozna_z_indeksi polinom 0 ""



(* let primer_3_8 = izpis [ 1; 2; 1 ] *)
(* let primer_3_9 = izpis [ 1; 0; -1; 0; 1; 0; -1; 0; 1; 0; -1; 0; 1 ] *)
(* let primer_3_10 = izpis [ 0; -3; 3; -1 ] *)

(* ## Samodejno odvajanje ****************************************************************************************)

let priblizek_odvoda f x0 h = (f (x0 +. h) -. f x0) /. h

(* let primer_3_11 =
   let f x = sin x +. cos x +. exp x in
   List.map (priblizek_odvoda f 1.) [ 0.1; 0.01; 0.001; 0.0001; 0.00001 ] *)

type odvedljiva = (float -> float) * (float -> float)

let sinus : odvedljiva = (sin, cos)
let kosinus : odvedljiva = (cos, fun x -> -.sin x)
let eksp : odvedljiva = (exp, exp)

let ( ++. ) : odvedljiva -> odvedljiva -> odvedljiva =
 (* pozorni bodite, da anonimni funkciji v paru date med oklepaje *)
 fun (f, f') (g, g') -> ((fun x -> f x +. g x), fun x -> f' x +. g' x)

(* let primer_3_12 =
   let _, f' = sinus ++. kosinus ++. eksp in
   f' 1. *)

(** Vrednost odvoda *)

let vrednost ((f, f') : odvedljiva) x = f x

let odvod ((f, f') : odvedljiva) x = f' x

(** Osnovne funkcije *)


let konstanta (c : float) : odvedljiva =
   ((fun x -> c), (fun x -> 0.0))
 
let identiteta : odvedljiva =
   ((fun x -> x), (fun x -> 1.))

(** Produkt in kvocient *)



let ( **. ) ((f, f'): odvedljiva) ((g, g'): odvedljiva) : odvedljiva = 
  ((fun x -> f x *. g x), (fun x -> f' x *. g x +. f x *. g' x))

let ( //. ) ((f, f'): odvedljiva) ((g, g'): odvedljiva) : odvedljiva = 
  ((fun x -> f x /. g x), (fun x -> (f' x *. g x -. f x *. g' x) /. (g x *. g x)))
(* let kvadrat = identiteta **. identiteta *)

(** Kompozitum *)


let ( @@. ) ((f, f'): odvedljiva) ((g, g'): odvedljiva) : odvedljiva = 
  ((fun x -> f (g x)), (fun x -> f' (g x) *. g' x))
(* let vedno_ena = (kvadrat @@. sinus) ++. (kvadrat @@. kosinus) *)
(* let primer_4_1 = vrednost vedno_ena 12345. *)
(* let primer_4_2 = odvod vedno_ena 12345. *)

(* ## Substitucijska šifra *********************************************************************************)

let quick_brown_fox = "THEQUICKBRWNFXJMPSOVLAZYDG"
let rot13 = "NOPQRSTUVWXYZABCDEFGHIJKLM"
let indeks c = Char.code c - Char.code 'A'
let crka i = Char.chr (i + Char.code 'A')

(** Šifriranje *)


let sifriraj kljuc niz = 
   let sifriraj_crka kljuc znak =
     if 'A' <= znak && znak <= 'Z'
       then String.get kljuc (indeks znak)
     else znak
   in
   String.map (sifriraj_crka kljuc) niz
(* let primer_5_1 = sifriraj quick_brown_fox "HELLO, WORLD!" *)
(* let primer_5_2 = "VENI, VIDI, VICI" |> sifriraj rot13 *)
(* let primer_5_3 = "VENI, VIDI, VICI" |> sifriraj rot13 |> sifriraj rot13 *)

(** Inverzni ključ *)


let inverz kljuc =
  let po_abecedi =
    let dolzina_abecede = String.length kljuc in
    let rec prvi_del_abecede_dolzine_n n nov =
      match n with
      | -1 -> String.concat "" nov
      | _ -> prvi_del_abecede_dolzine_n (n - 1) (String.make 1 (crka n) :: nov)
    in
    prvi_del_abecede_dolzine_n (dolzina_abecede - 1) []
  in  
  let inverz_crka kljuc znak =
    crka (String.index kljuc znak)
  in
  String.map (inverz_crka kljuc) po_abecedi
(* let primer_5_4 = inverz quick_brown_fox *)
(* let primer_5_5 = inverz rot13 = rot13 *)
(* let primer_5_6 = inverz "BCDEA" *)

(** Ugibanje ključa *)

let besede =
  "the of to and a in is it you that he was for on are with as i his they be \
   at one have this from or had by word but what some we can out other were \
   all there when up use your how said an each she which do their time if will \
   way about many then them write would like so these her long make thing see \
   him two has look more day could go come did number sound no most people my \
   over know water than call first who may down side been now find any new \
   work part take get place made live where after back little only round man \
   year came show every good me give our under name very through just form \
   sentence great think say help low line differ turn cause much mean before \
   move right boy old too same tell does set three want air well also play \
   small end put home read hand port large spell add even land here must big \
   high such follow act why ask men change went light kind off need house \
   picture try us again animal point mother world near build self earth father \
   head stand own page should country found answer school grow study still \
   learn plant cover food sun four between state keep eye never last let \
   thought city tree cross farm hard start might story saw far sea draw left \
   late run don't while press close night real life few north open seem \
   together next white children begin got walk example ease paper group always \
   music those both mark often letter until mile river car feet care second \
   book carry took science eat room friend began idea fish mountain stop once \
   base hear horse cut sure watch color face wood main enough plain girl usual \
   young ready above ever red list though feel talk bird soon body dog family \
   direct pose leave song measure door product black short numeral class wind \
   question happen complete ship area half rock order fire south problem piece \
   told knew pass since top whole king space heard best hour better true . \
   during hundred five remember step early hold west ground interest reach \
   fast verb sing listen six table travel less morning ten simple several \
   vowel toward war lay against pattern slow center love person money serve \
   appear road map rain rule govern pull cold notice voice unit power town \
   fine certain fly fall lead cry dark machine note wait plan figure star box \
   noun field rest correct able pound done beauty drive stoDo contain front \
   teach week final gave green oh quick develop ocean warm free minute strong \
   special mind behind clear tail produce fact street inch multiply nothing \
   course stay wheel full force blue object decide surface deep moon island \
   foot system busy test record boat common gold possible plane stead dry \
   wonder laugh thousand ago ran check game shape equate hot miss brought heat \
   snow tire bring yes distant fill east paint language among grand ball yet \
   wave drop heart am present heavy dance engine position arm wide sail \
   material size vary settle speak weight general ice matter circle pair \
   include divide syllable felt perhaps pick sudden count square reason length \
   represent art subject region energy hunt probable bed brother egg ride cell \
   believe fraction forest sit race window store summer train sleep prove lone \
   leg exercise wall catch mount wish sky board joy winter sat written wild \
   instrument kept glass grass cow job edge sign visit past soft fun bright \
   gas weather month million bear finish happy hope flower clothe strange gone \
   jump baby eight village meet root buy raise solve metal whether push seven \
   paragraph third shall held hair describe cook floor either result burn hill \
   safe cat century consider type law bit coast copy phrase silent tall sand \
   soil roll temperature finger industry value fight lie beat excite natural \
   view sense ear else quite broke case middle kill son lake moment scale loud \
   spring observe child straight consonant nation dictionary milk speed method \
   organ pay age section dress cloud surprise quiet stone tiny climb cool \
   design poor lot experiment bottom key iron single stick flat twenty skin \
   smile crease hole trade melody trip office receive row mouth exact symbol \
   die least trouble shout except wrote seed tone join suggest clean break \
   lady yard rise bad blow oil blood touch grew cent mix team wire cost lost \
   brown wear garden equal sent choose fell fit flow fair bank collect save \
   control decimal gentle woman captain practice separate difficult doctor \
   please protect noon whose locate ring character insect caught period \
   indicate radio spoke atom human history effect electric expect crop modern \
   element hit student corner party supply bone rail imagine provide agree \
   thus capital won't chair danger fruit rich thick soldier process operate \
   guess necessary sharp wing create neighbor wash bat rather crowd corn \
   compare poem string bell depend meat rub tube famous dollar stream fear \
   sight thin triangle planet hurry chief colony clock mine tie enter major \
   fresh search send yellow gun allow print dead spot desert suit current lift \
   rose continue block chart hat sell success company subtract event \
   particular deal swim term opposite wife shoe shoulder spread arrange camp \
   invent cotton born determine quart nine truck noise level chance gather \
   shop stretch throw shine property column molecule select wrong gray repeat \
   require broad prepare salt nose plural anger claim continent oxygen sugar \
   death pretty skill women season solution magnet silver thank branch match \
   suffix especially fig afraid huge sister steel discuss forward similar \
   guide experience score apple bought led pitch coat mass card band rope slip \
   win dream evening condition feed tool total basic smell valley nor double \
   seat arrive master track parent shore division sheet substance favor \
   connect post spend chord fat glad original share station dad bread charge \
   proper bar offer segment slave duck instant market degree populate chick \
   dear enemy reply drink occur support speech nature range steam motion path \
   liquid log meant quotient teeth shell neck"


let slovar = String.split_on_char ' ' (String.uppercase_ascii besede)
(* let primer_5_7 = take 42 slovar *)
(* let primer_5_8 = List.nth slovar 321 *)

(* Med ugibanjem seveda ne bomo poznali celotnega ključa. V tem primeru bomo za neznane črke uporabili znak `_`. Na primer, če bi vedeli, da je črka `A` v besedilu šifrirana kot `X`, črka `C` pa kot `Y`, bi ključ zapisali kot `"X_Y_______________________"`. *)
(*  *)
(* Napišite funkcijo `dodaj_zamenjavo : string -> char * char -> string option`, ki sprejme ključ ter ga poskusi razširiti z zamenjavo dane črke. Funkcija naj vrne `None`, če razširitev vodi v ključ, ki ni bijektiven (torej če ima črka že dodeljeno drugo zamenjavo ali če smo isto zamenjavo dodelili dvema različnima črkama). *)

(** Razširjanje ključa s črko *)

let dodaj_zamenjavo kljuc (prva_crka, druga_crka) : string option = 
  let mesto_crke = indeks prva_crka in
  let rec zamenjava_crke_v_nizu niz (crka: char) n =
    if n >= String.length niz then
      "" 
    else
      let znak = String.get niz n in
      let nov_znak = if n = mesto_crke then crka else znak in
      (String.make 1 nov_znak) ^ zamenjava_crke_v_nizu niz crka (n + 1) 
  in
  if mesto_crke >= String.length kljuc then None 
  else
    match String.get kljuc mesto_crke with
    | a when a = druga_crka -> Some kljuc
    | '_' -> Some (zamenjava_crke_v_nizu kljuc druga_crka 0)
    | _ -> None



(* let primer_5_9 = dodaj_zamenjavo "AB__E" ('C', 'X') *)
(* let primer_5_10 = dodaj_zamenjavo "ABX_E" ('C', 'X') *)
(* let primer_5_11 = dodaj_zamenjavo "ABY_E" ('C', 'E') *)

(** Razširjanje ključa z besedo *)

(* S pomočjo funkcije `dodaj_zamenjavo` sestavite še funkcijo `dodaj_zamenjave : string -> string * string -> string option`, ki ključ razširi z zamenjavami, ki prvo besedo preslikajo v drugo. *)


let dodaj_zamenjave kljuc (prva_beseda, druga_beseda) =
   let dolzina_besed = 
     if String.length prva_beseda = String.length druga_beseda then String.length prva_beseda 
     else 0
   in
   if dolzina_besed = 0 then None 
   else
     let rec po_vseh_indeksih n niz =
       if n >= dolzina_besed then Some niz
       else
         match dodaj_zamenjavo niz ((String.get prva_beseda n), (String.get druga_beseda n)) with
         | Some nov_niz -> po_vseh_indeksih (n + 1) nov_niz
         | None -> None
     in 
     po_vseh_indeksih 0 kljuc
(* let primer_5_12 = dodaj_zamenjave "__________________________" ("HELLO", "KUNNJ") *)
(* let primer_5_13 = dodaj_zamenjave "ABCDU_____________________" ("HELLO", "KUNNJ") *)
(* let primer_5_14 = dodaj_zamenjave "ABCDE_____________________" ("HELLO", "KUNNJ") *)

(** Vse možne razširitve *)

(* Sestavite funkcijo `mozne_razsiritve : string -> string -> string list -> string list`, ki vzame ključ, šifrirano besedo ter slovar vseh možnih besed, vrne pa seznam vseh možnih razširitev ključa, ki šifrirano besedo slikajo v eno od besed v slovarju. *)


let mozne_razsiritve kljuc beseda seznam_besed = 
  let rec besede_po_indeksih seznam nov =
  match seznam with
  | [] -> List.rev nov
  | prva_beseda :: ostale_besede -> 
    match dodaj_zamenjave kljuc (beseda, prva_beseda) with
    | Some zamenjava -> besede_po_indeksih ostale_besede (zamenjava :: nov) 
    | None -> besede_po_indeksih ostale_besede nov 
  in
  besede_po_indeksih seznam_besed []
 

(* let primer_5_15 =
   slovar
   |> mozne_razsiritve (String.make 26 '_') "KUNNJ"
   |> List.map (fun kljuc -> (kljuc, sifriraj kljuc "KUNNJ")) *)

(** Odšifriranje *)

(* Napišite funkcijo `odsifriraj : string -> string option`, ki sprejme šifrirano besedilo in s pomočjo slovarja besed ugane odšifrirano besedilo. Funkcija naj vrne `None`, če ni mogoče najti nobenega ustreznega ključa. *)
let odsifriraj besedilo = 
  (*vrne prvo od moznosti ali None*)
  let sez_besed =
    if besedilo = "" then failwith "Besedilo je prazno, obstaja neskončno ključev."
    else String.split_on_char ' ' (String.uppercase_ascii besedilo)  in

  let kljuc = String.make 26 '_' in 
    
  let zakljuci mozni_kljuci = 
    match mozni_kljuci with
    | [] -> None
    | prvi :: vsi_ostali -> Some (sifriraj prvi besedilo)
  in
  (*  (če želimo vse rešitve)
    let sifriraj_vse_kljuce kljuc = sifriraj kljuc besedilo in
      let zakljuci mozni_kljuci = 
        match mozni_kljuci with
        | [] -> None
        | _ -> Some (List.map sifriraj_vse_kljuce mozni_kljuci)
      in 
  *)
  let rec pojdi_po_vseh_besedah trenutni_kljuci besede =
    match besede with 
    | [] -> zakljuci trenutni_kljuci
    | prva_beseda :: preostal_seznam -> 
        let rec pojdi_po_kljucih dobljeni_kljuci novi_kljuci = 
        match dobljeni_kljuci with
        | [] -> pojdi_po_vseh_besedah (List.flatten novi_kljuci) preostal_seznam
        | prvi_kljuc :: ostali_kljuci -> 
          let dodaj_kljuce = mozne_razsiritve prvi_kljuc prva_beseda slovar in 
          let poglej_ce_je_kljuc_ze_notri klc =
            if List.mem klc novi_kljuci then novi_kljuci 
            else klc :: novi_kljuci
          in
          pojdi_po_kljucih ostali_kljuci (poglej_ce_je_kljuc_ze_notri dodaj_kljuce)
      in pojdi_po_kljucih trenutni_kljuci []
  in pojdi_po_vseh_besedah [kljuc] sez_besed
(*Se opravičujem, ampak tale funkcija mi za dani primer melje tri minute, saj poišče vse možne ključe, vrne pa le prvega. 
Da bi vrnil vse bi le pri funkciji zakljuci moral besedilo zasifrirati z vsemi kljuci. To se mi je zdelo uporabno, 
ker so včasih vrnjena besedila kljub pravilnim besedam nesmiselna.*)     
    
(* let primer_5_16 = sifriraj quick_brown_fox "THIS IS A VERY HARD PROBLEM" *)
(* let primer_5_17 = odsifriraj "VKBO BO T AUSD KTSQ MSJHNUF" *)
