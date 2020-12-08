# ProiectPLP-SimpleC
Imi propun sa-mi definesc in coq propriul limbaj de programare asemanator limbajului C, denumit SimpleC.

Toate instructiunile de mai jos sunt inspirate de la cele existente in limbajul de programare C.
``` Limbajul va avea urmatoarele functionalitati:
-tipuri de variabile + declarare de variabile de aceste tipuri - numere naturale, bool, string, pointeri

-operatii pe numere naturale: (+', -', *', /', %', ^')

-operatii pe valori booleene: (<', <=', >', >=', !=', ==', &&', ||', !')

-operatii pe string-uri: (concat())

-operatii de conversie intre tipuri: (toBool(), toNat(), toString())

-instructiunea de atribuire

-instructiuni conditionale: if' (conditie) {bloc} end'
             if' (conditie) {bloc} else' {bloc} end'
             switch (expresie aritmetica) {case cons1: {bloc}; case const2: {bloc}; ... default: {bloc}; } end'
                            
-instructiuni repetitive: while' (conditie) {bloc} end'
             do' {bloc} while' (conditie) end'
             for (initializare, conditie, expresie) {bloc} end'
                          
-instructiuni speciale: break (pentru a iesi fortat dintr-o bucla)
             continue (pentru a trece direct la urmatoarea iteratie dintr-o bucla)
                       
-functii, apeluri de functii; functia obligatorie main -- fun main() {corp functie}
             alte functii -- fun nume_functie () {corp functie}
                              
-variabile locale, variabile globale (definite inafara functiei main)```
