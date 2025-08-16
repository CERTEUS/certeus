# +-------------------------------------------------------------+
# |                         CERTEUS                             |
# |                        LEXLOG RULES                         |
# +-------------------------------------------------------------+
# | FILE: packs/jurisdictions/PL/rules/kk.lex                   |
# | ROLE: Minimal rules for KK-286 (fraud), ASCII-safe.         |
# +-------------------------------------------------------------+

# logical variables
DEFINE oszustwo_stwierdzone: Bool
DEFINE cel_korzysci_majatkowej: Bool
DEFINE wprowadzenie_w_blad: Bool
DEFINE niekorzystne_rozporzadzenie_mieniem: Bool

# premises (labels are human-readable)
PREMISE P_CEL: "Cel osiagniecia korzysci majatkowej"
    EXISTS (fact: FACTLOG WHERE role = 'intent_financial_gain')
    MAPS_TO (cel_korzysci_majatkowej)

PREMISE P_WPROWADZENIE: "Wprowadzenie w blad"
    EXISTS (fact: FACTLOG WHERE role = 'act_deception')
    MAPS_TO (wprowadzenie_w_blad)

PREMISE P_ROZPORZADZENIE: "Niekorzystne rozporzadzenie mieniem"
    EXISTS (fact: FACTLOG WHERE role = 'detrimental_property_disposal')
    MAPS_TO (niekorzystne_rozporzadzenie_mieniem)

# rule: all three premises required
RULE R_286_OSZUSTWO (P_CEL, P_WPROWADZENIE, P_ROZPORZADZENIE) -> K_OSZUSTWO_STWIERDZONE

# conclusion
CONCLUSION K_OSZUSTWO_STWIERDZONE: "Czyn wypelnia znamiona oszustwa z art. 286 k.k."
    ASSERT (oszustwo_stwierdzone == (cel_korzysci_majatkowej AND wprowadzenie_w_blad AND niekorzystne_rozporzadzenie_mieniem))