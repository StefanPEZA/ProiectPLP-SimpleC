# ProiectPLP-SimpleC
Imi propun sa-mi definesc in coq propriul limbaj de programare asemanator limbajului C, denumit SimpleC.

Limbajul va avea urmatoarele functionlitati si instructiuni, inspirate din limbajul C. (Sintactica si semantica putin modificate)
```-tipuri de variabile + declarare de variabile de aceste tipuri - numere naturale, bool, string
-operatii pe numere naturale: (+', -', *', /', %', ^')
-operatii pe valori booleene: (<', <=', >', >=', !=', ==', &&', ||', !', xor'(sau exclusiv), xand'(si exclusiv))
-operatii pe stringuri (concat(str1, str2), strlen(str))
-operatii de conversie intre tipuri: (toBool(nat), toNat(bool/string), toString(nat/bool))
-instructiunea de atribuire
-instructiuni conditionale: if' (conditie) {stmt} end'
             if' (conditie) {stmt} else' {stmt} end'
             switch (expresie aritmetica) {case cons1: {stmt}; case const2: {stmt}; ... default: {stmt}; } end'
-instructiuni repetitive: while' (conditie) {stmt} end'
             do' {stmt} while' (conditie) end'
             for (initializare, conditie, asignare) {stmt} end'
-instructiuni speciale: break (pentru a iesi fortat dintr-o bucla)
             continue (pentru a trece direct la urmatoarea iteratie dintr-o bucla)
-functii, apeluri de functii; functia obligatorie main -- void main() {stmt}
             alte functii -- void nume_functie(argumente) {stmt} defineste o functie care nu returneaza nimic
-variabile locale (in interiorul unei functii), variabile globale (definite inafara functiei main)
-functii de input/output: read(variabila) citeste input-ul si-l pune intr-o variabila
	     write_str(string) - afiseaza un mesaj, write(variabila) - afiseaza valoarea unei variabile```
