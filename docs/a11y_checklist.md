<!--
CERTEUS — A11y Checklist (WCAG 2.2 AA baseline)
-->

# A11y Checklist — WCAG 2.2 AA (Baseline)

- Lang: element `<html>` posiada atrybut `lang` zgodny z treścią (PL/EN).
- Tytuł: `<title>` obecny i niepusty.
- Viewport: `<meta name="viewport" ...>` obecny.
- Struktura: co najmniej jedno `<h1>` na stronę; logiczna hierarchia nagłówków.
- Landmarki: obecność `<main>` lub semantycznych sekcji/ARIA (`role="main"` itp.).
- Obrazy: wszystkie `<img>` posiadają `alt` (puste do dekoracyjnych, opisowe dla treściowych).
- Linki/przyciski: czytelny tekst lub `aria-label`/`title`; brak „gołego” ikono‑linku bez opisu.
- Kontrast: przycisk/tekst spełnia AA (kontrola manualna + narzędzia devtools).
- Klawiatura: elementy interaktywne fokusowalne (`tabindex` tylko gdy konieczne); brak pułapek fokusa (kontrola manualna).

Raport: testy automatyczne pokrywają obecność i podstawy semantyki; pełny audyt kontrastu/klawiatury wykonywany manualnie (demo tygodnia).

