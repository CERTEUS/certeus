---
name: "Release polish (LITE)"
about: Checklist jakości publicznego mirrora przed/po publikacji
title: "Release polish – YYYY-MM-DD"
labels: ["release", "docs", "public-lite"]
assignees: []
---

## ✅ Checklist (zaznacz, gdy OK)

- [ ] Social preview ustawione (PNG og.png wgrane w Settings → General → Social preview)
- [ ] Pages działają (200/OK) – strona główna + /api/overview/
- [ ] OG / favicon (CDN-BUST): `og.<rev>.svg` i `favicon.<rev>.ico` = **200/OK**
- [ ] PROVENANCE.md zaktualizowane (Source + Published + AssetRev)
- [ ] PROVENANCE_HISTORY.md dopisany nowy wiersz
- [ ] Policy-Scan = zielone (brak niedozwolonych ścieżek)
- [ ] CI-Public-Light = zielone (link-check)
- [ ] Policies-Report = wygenerowany artefakt
- [ ] README (CTA + kontakt) aktualne

> `rev` = `AssetRev` z **PROVENANCE.md**

