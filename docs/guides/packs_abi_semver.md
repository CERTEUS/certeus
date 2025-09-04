# Packs ABI/SemVer — zasady i praktyka

SemVer: `MAJOR.MINOR.PATCH`
- MAJOR: zmiany łamiące ABI (np. inna arność `register`, usunięcie klasy `Plugin`, zmiana wymaganego interfejsu)
- MINOR: rozszerzenia kompatybilne (nowe możliwości przy zachowaniu dotychczasowego ABI)
- PATCH: poprawki bez wpływu na ABI

Deskryptor ABI zbierany przez `scripts/gates/pack_abi_semver_gate.py`:
- `module`: ścieżka modułu (np. `plugins.foo.src.main`)
- `has_module_register` + `module_register_arity`
- `has_class_plugin` + `has_class_register` + `class_register_arity`

Workflow deweloperski:
1) Zmień kod pluginu (np. dodaj parametr do `register`).
2) Uruchom gate ABI/SemVer: `python scripts/gates/pack_abi_semver_gate.py`.
   - Jeśli baseline istnieje i ABI się zmieniło, gate zgłosi problem.
3) Zwiększ `MAJOR` w `plugins/<pack>/plugin.yaml` (np. 1.1.0 → 2.0.0).
4) Zaktualizuj baseline: `python scripts/packs/update_abi_baselines.py`.
5) Uruchom testy i gate’y (ci‑gates w PR opublikuje podsumowanie).

Enforce (opcja): ustaw `ENFORCE_PACK_ABI_SEMVER=1` w środowisku CI, jeśli chcesz blokować PR przy naruszeniach.

Dobre praktyki:
- Zmieniaj ABI tylko z uzasadnieniem i changelogiem.
- Dodawaj testy kontraktowe dla `register`/`Plugin.register` (arity, zachowanie).
- Wersjonuj manifesty i publikuj notki migracyjne dla integratorów.

