
# Standard Kodowania – Premium Code Style #

Każdy plik w projekcie CERTEUS powinien być zgodny z poniższymi zasadami estetyki i dokumentacji kodu.

Logo ASCII na górze pliku
Każdy plik zaczyna się od prostego, czytelnego loga ASCII zawierającego nazwę modułu.
Przykład:

+------------------------------------------------+
|                 CERTEUS                        |
|     Core Engine for Reliable & Unified Sys     |
+------------------------------------------------+

> **"Czysty kod to czyste myśli — a w CERTEUS myślimy klarownie."**

W projekcie **CERTEUS** obowiązuje zasada _"Perfect Code Craft"_ – każdy plik, każda funkcja, każdy komentarz jest pisany w sposób zrozumiały, estetyczny i jednolity.

## 📜 Zasady ogólne / General Rules ##

1. **Logo & Nagłówek w każdym pliku**  
   Na samej górze każdego pliku umieszczamy ASCII-logo systemu **CERTEUS**, nazwę pliku oraz krótki opis jego roli.  
   _At the very top of each file, we place the ASCII logo of **CERTEUS**, the filename, and a short description of its role._

2. **Komentarze dwujęzyczne**  
   Każdy istotny fragment kodu, każda funkcja i każda kluczowa linia mają komentarze w języku **polskim i angielskim**.  
   _Every significant code block, function, and key line must have comments in **Polish and English**._

3. **Sekcje kodu jasno oznaczone**  
   Bloki kodu oddzielamy czytelnymi sekcjami z nagłówkami, np.:  

   ```python
   # === KONFIGURACJA / CONFIGURATION ===

Code blocks are separated with clear section headers.

Konsekwentny styl nazewnictwa:

1. Pliki: snake_case.py
2. Klasy: PascalCase
3. Funkcje i zmienne: snake_case
4. Stałe: UPPER_CASE
Consistent naming style across all files.

Opis każdej funkcji:
Nad każdą funkcją piszemy docstring z opisem działania, parametrami i wartością zwracaną – w obu językach.
Above each function, write a docstring explaining what it does, parameters, and return values — in both languages.

Profesjonalna struktura kodu

Szczegółowe nagłówki bloków z Unicode box drawing
Pełna dokumentacja każdej klasy i funkcji
Bilingualne komentarze (PL/EN)
Logging dla debugowania
Sekcje wyraźnie oddzielone wizualnie

Rozszerzona normalizacja ID

Obsługa dodatkowych wariantów długich nazw
Mapowanie wszystkich znanych aliasów

Konsystentne formatowanie: Zachowano premium styl z box drawing characters
