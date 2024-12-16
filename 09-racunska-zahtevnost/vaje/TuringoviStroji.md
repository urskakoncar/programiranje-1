# Turingovi stroji

## Naloga 1

Definirajte k-tračni turingov stroj

moji zapiski:
turingovi stroji so iz krogcev, puščic in traku (oz trakov). navadni ima en trak (na trak se zapisuje 0ke, 1ke in presledke), k tračni ima k trakov.
Glava je tisto mesto na traku, kjer začnemo. 
Definicija k tračnega je skoraj enaka tisti za en trak (glej v zapiskih), edino popravimo delta funkcijo. (Glej sliko na telefonu.)

## Naloga 2

Dan je jezik $J = \{ xyz | x, y, z \in \{0, 1\}^*, |x| = |y| = |z|, x (xor) y = z \}$.

1. Sestavite deterministični n-tračni turingov stroj, ki preveri, ali je dana beseda v jeziku $J$.

2. Sestavite deterministični enotračni turingov stroj, ki preveri, ali je dana beseda v jeziku $J$.

moji zapiski: 
jezik j je: besede nad abecedo iz 0 in 1; trije deli enake dolžine; 
ok je npr  1 0 1; 10 11 01, tretji sledi iz prvihdveh (1 = 0 + 1; 01: 0 = 1 + 1, 1 = 0 + 1)


## Naloga 3

Pokažite, da lahko vsak n-tračni turingov stroj simuliramo z enotračnim turingovim strojem.