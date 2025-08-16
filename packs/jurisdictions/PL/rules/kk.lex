+-------------------------------------------------------------+
|              CERTEUS - LEXLOG Rules for Poland              |
+-------------------------------------------------------------+
| PLIK: kk.lex                                                |
| ROLA/ROLE: Formalizacja reguł z polskiego Kodeksu Karnego.  |
|            MVP: art. 286 (Oszustwo).                        |
+-------------------------------------------------------------+

# === SEKCJA: Art. 286 k.k. - Oszustwo / SECTION: Art. 286 P.C. - Fraud ===

# --- Definicje Zmiennych Logicznych / Logical Variable Definitions ---
DEFINE oszustwo_stwierdzone: Bool
DEFINE cel_korzysci_majatkowej: Bool
DEFINE wprowadzenie_w_blad: Bool
DEFINE niekorzystne_rozporzadzenie_mieniem: Bool

# --- Przesłanki (powiązanie z faktami) / Premises (link to facts) ---
PREMISE P_CEL: "Działanie w celu osiągnięcia korzyści majątkowej"
    EXISTS (fact: FACTLOG WHERE role = 'intent_financial_gain')
    MAPS_TO (cel_korzysci_majatkowej)

PREMISE P_WPROWADZENIE: "Doprowadzenie do rozporządzenia mieniem poprzez wprowadzenie w błąd"
    EXISTS (fact: FACTLOG WHERE role = 'act_deception')
    MAPS_TO (wprowadzenie_w_blad)

PREMISE P_ROZPORZADZENIE: "Wystąpiło niekorzystne rozporządzenie mieniem"
    EXISTS (fact: FACTLOG WHERE role = 'detrimental_property_disposal')
    MAPS_TO (niekorzystne_rozporzadzenie_mieniem)

# --- Reguła Logiczna / Logical Rule ---
RULE R_286_OSZUSTWO (P_CEL, P_WPROWADZENIE, P_ROZPORZADZENIE) -> K_OSZUSTWO_STWIERDZONE

# --- Konkluzja / Conclusion ---
CONCLUSION K_OSZUSTWO_STWIERDZONE: "Czyn wypełnia znamiona oszustwa z art. 286 k.k."
    ASSERT (oszustwo_stwierdzone == (cel_korzysci_majatkowej AND wprowadzenie_w_blad AND niekorzystne_rozporzadzenie_mieniem))
