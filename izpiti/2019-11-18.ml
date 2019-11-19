(* =================== *)
(* 1. naloga: funkcije *)
(* =================== *)

let is_root x y = if x <0 then false else (x * x = y)

let pack3 x y z = (x, y, z)

let rec sum_if_not predikat list =
  let rec sum_if_not' predikat list acc =
    match list with
    | [] -> acc
    | x :: xs -> if (predikat x) then (sum_if_not' predikat xs acc) else (sum_if_not' predikat xs (acc + x))
  in
  sum_if_not' predikat list 0

let rec map f list = 
  match list with
  | [] -> []
  | x :: xs -> f x :: map f xs

let rec reverse list =
  let rec rev list acc =
    match list with 
    | [] -> acc
    | x :: xs -> rev xs (x :: acc)
  in
  rev list []

let rec apply list_f list_int =
  let rec apply' list_f list_int acc =
    match list_f with
    | [] -> acc
    | x :: xs -> apply' (xs list_int ((map x list_int ) :: acc))
  in 
  reverse (apply' list_f list_int [])

(* ======================================= *)
(* 2. naloga: podatkovni tipi in rekurzija *)
(* ======================================= *)

type vrsta_srecanja = 
  | Predavanja
  | Vaje

type srecanje = {
  predmet : string;
  vrsta : vrsta_srecanja;
  trajanje : int;
}
(*type urnik = 
  | Urnik of (list of srecanje) * (list of int)*)

let vaje = {predmet = "Analiza 2a"; vrsta = Vaje; trajanje = 2}

let predavanje = {predmet = "Programiranje 1"; vrsta = Predavanja; trajanje = 2}

let urnik_profesor () = failwith "dopolni me"

let je_preobremenjen () = failwith "dopolni me"

let bogastvo () = failwith "dopolni me"