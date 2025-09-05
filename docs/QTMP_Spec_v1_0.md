# Kwantowa Teoria Pomiaru Prawnego (QTMP) – Specyfikacja v1.0

**Data:** 2025-08-29

To jest finalna, kopiowalna specyfikacja warstwy _pomiaru_ w architekturze CERTEUS: domyka trylogię **fizyka → geometria → pomiar**. Dokument jest gotowy do włączenia do repo (docs/) oraz do cytowania w PCO jako _Measurement Postulate_.

---

## 1. Funkcja Falowa Sprawy (|Ψ_case⟩)

Stan sprawy przed rozstrzygnięciem jest wektorem w przestrzeni Hilberta, opisującym superpozycję wszystkich możliwych werdyktów.

```latex
$$
\ket{\Psi_{\text{case}}} = \sum_i c_i \ket{\text{werdykt}_i}
$$
```

- \(\ket{\Psi\_{\text{case}}}\): stan kwantowy całej sprawy.
- \(\ket{\text{werdykt}\_i}\): stany bazowe (np. `ALLOW`, `DENY`, `ABSTAIN`).
- \(c_i\): amplitudy prawdopodobieństwa; \(|c_i|^2\) to prawdopodobieństwo uzyskania danego werdyktu.

---

## 2. Operatory Obserwabli Prawnych (\(\hat{O}\))

Każde pytanie prawne to operator hermitowski (\(\hat{O} = \hat{O}^\dagger\)), którego wartości własne są jedynymi możliwymi wynikami pomiaru.

- **Operator Werdyktu (\(\hat{W}\))** — wartości własne: `ALLOW`, `DENY`, `ABSTAIN`.
- **Operator Zamiaru (\(\hat{I}\))** — wartości własne: `dolus directus`, `dolus eventualis`, `culpa`.
- **Operator „Litery Prawa” (\(\hat{L}\))** vs. **Operator „Ducha Prawa” (\(\hat{T}\))** — w ogólności niekomutujące.

---

## 3. Zasada Nieoznaczoności Prawa (Heisenberg)

Jeśli dwa operatory (pytania) nie komutują, nie można poznać obu odpowiedzi jednocześnie z pełną precyzją.

```latex
$$
\Delta L \cdot \Delta T \ge \frac{1}{2} \Big|\langle [\hat{L},\,\hat{T}] \rangle\Big|
$$
```

Gdy \([\hat{L},\hat{T}] \neq 0\): im precyzyjniej „litera prawa”, tym bardziej rozmywa się „duch prawa” (i odwrotnie) — **fundamentalny, mierzalny dylemat interpretacyjny**.

---

## 4. Splątanie Dowodowe (Evidentiary Entanglement)

Dwa (lub więcej) dowodów mogą tworzyć jeden, nierozerwalny stan kwantowy. Pomiar jednego natychmiast determinuje stan drugiego.

- Przykładowy stan splątany dwóch dowodów A, B:

  ```latex
  $$
  \ket{\Psi_{AB}} = \tfrac{1}{\sqrt{2}}\big(\ket{0_A1_B} - \ket{1_A0_B}\big)
  $$
  ```

- Mierniki splątania: **wzajemna informacja**, **negatywność** (N>0 ⇒ splątanie).

---

## 5. Kolaps i Dekoherecja

Interakcja z otoczeniem (akt obserwacji, decyzja sędziego) niszczy superpozycję (dekoherencja) i powoduje **kolaps funkcji falowej** do jednego, klasycznego werdyktu.

- Proces pomiaru (Lüders / projekcyjny):

  ```latex
  $$
  \rho \;\longrightarrow\; \sum_i \hat{P}_i \, \rho \, \hat{P}_i^{\dagger},\qquad \hat{P}_i=\ket{i}\!\bra{i}
  $$
  ```

- **Czas dekoherencji** = KPI: jak szybko sprawa „zastyga” w jednym rozwiązaniu.

---

## 6. Interfejs implementacyjny (qtm-spec)

Minimalne punkty zaczepienia (współpraca z `lexqft` i `cfe`):

```python
from qtm.state import HilbertSpace, pure_state
from qtm.ops import hermitian_from_eigs, commutator, uncertainty_lower_bound
from qtm.measure import measure_projective
from qtm.channels import dephasing, depolarizing

H = HilbertSpace(["ALLOW","DENY","ABSTAIN"])                    # baza werdyktu
s = pure_state(H, {"ALLOW":1+0j, "DENY":1j, "ABSTAIN":0.2})      # |Ψ_case>

W = hermitian_from_eigs(H, {"ALLOW":+1, "DENY":-1, "ABSTAIN":0}) # operator werdyktu
L = hermitian_from_eigs(H, {"ALLOW":0.9, "DENY":0.1, "ABSTAIN":0.5})
T = hermitian_from_eigs(H, {"ALLOW":0.2, "DENY":0.8, "ABSTAIN":0.6})

lb = uncertainty_lower_bound(s.rho, L, T)   # dolna granica nieoznaczoności
outcome, p, s2 = measure_projective(s, H, {"ALLOW":+1,"DENY":-1,"ABSTAIN":0})
s3 = dephasing(s2, p=0.3)                   # dekoherencja (ekspozycja publiczna)
```

---

## 7. Telemetria PCO (pola do dopięcia)

- `qtm.collapse_outcome` ∈ {ALLOW, DENY, ABSTAIN}
- `qtm.collapse_prob` ∈ [0,1]
- `qtm.collapse_latency_ms`
- `qtm.decoherence.channel` ∈ {dephasing, depolarizing, damping}
- `qtm.uncertainty_bound.L_T` (wartość \(\tfrac12 |\langle [\hat L, \hat T] \rangle|\))
- `qtm.entanglement.mi`, `qtm.entanglement.negativity`

---

## 8. Kryteria sukcesu (KPI)

- Zgodność rozkładów **Born vs. empiryka** (A/B spraw): \(R^2 \ge 0.9\)
- **Czas dekoherencji**: w reżimach pilnych krótki; w wątpliwych — długi, kontrolowany.
- **Uncertainty hits**: odsetek scenariuszy z \([\hat L,\hat T]\neq 0\) poprawnie raportowanych.
- **Entanglement alerts**: trafność wykrycia splątania (N>0) na walidacji krzyżowej.

---

## 9. Bezpieczniki i dobre praktyki

- Rejestruj **kolejność pomiarów** (niezamienne operatory!).
- Wszystkie kolapsy muszą zostawić **ślad w PCO** (czas, operator, wynik, p).
- Dekoherencja musi być jawna (kanał + parametry).
- Nie mieszaj baz (np. werdykt/intent) bez wyraźnego przełączenia operatorów i zapisania komutatora.

---

**Koniec specyfikacji QTMP v1.0.**
