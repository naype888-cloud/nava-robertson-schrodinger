import NavaRobertsonIndependent.Ontology.D29_ObserverSpectralMeasurement
import NavaRobertsonIndependent.Ontology.D30_FourChannelDistinctionCount
import NavaRobertsonIndependent.Ontology.D31_MeasurableExistenceBand
import NavaRobertsonIndependent.Ontology.D33_TorusPhaseThick
import NavaRobertsonIndependent.Ontology.D34_OpenEonRegistration
import NavaRobertsonIndependent.Ontology.D35_BanachHilbertABBridge
import NavaRobertsonIndependent.Ontology.D36_SeedAndH4Registration

/-!
# Layer 4 — Ontology

Observer, measurement and measurable existence. This layer depends only on
Layer 1 (no physical constant, no cosmology), and nothing else imports it; the
boundary is checked in `Verification/Layer4_Ontology.lean`. Its structures are
**postulates declared in their own signatures**, not derivations.

* `D29_ObservadorMedicionEspectral`: measurement as a declared postulate
  (`MedicionEspectral`) whose outcomes are the proved real spectrum of `A_d`
  (`D6`); no self-measurement (`no_auto_medida`).
* `D30_CuentaDistincionCuatroCanales`: under that postulate a measured triple of
  channels is a four-channel object (`cubo_medido_es_cuatro_canales`).
* `D31_BandaExistenciaMedible`: bundles `D9` + `D24` + `D30` into one statement.
  No new proof step; its conjuncts are independent facts, and its `4 ≤ d`
  hypothesis is supplied, not derived from the measurement data.
* `D33_FaseToroThick`: the seed has thick `0`; the torus (open eon) has thick
  `1/(r+1)`, never `0` nor `∞` (`toro_entre_cero_e_infinito`), and a nonzero
  thick forces the torus (`sin_cero_absoluto_implica_toro`). Reading: the thick
  is the thermal scale of the cell, so the open eon has no absolute zero.
* `D34_RegistroEonAbierto`: the registration hypothesis with content in every
  field — nonzero thick, rupture of the path (`D13`, the declared postulate
  "open eon ⇒ elementary dynamics with defect"), and a real spectral reading
  (`D29`) at each tick. Derived: the phase is the torus, `4 ≤ d`, every reading
  lies in `(−2, 2)`, and the defect lies in the band of `D31`, never `0`
  (`cierre_eon_abierto`). Satisfiable with real spectral readings
  (`registro_satisfacible`), not with `True` fields.
* `D35_PuenteBanachHilbertAB`: formalizes the model-specific rule that a
  relational reading factors through the norm distance `q(A,B)`, carries the
  three spatial coordinates from `H3` into `H4` with `q` as the fourth
  coordinate, and activates the torus at D13's first rupture `d=4`. The seed
  locates its three fermions and budget together; a germinated pair has two
  distinct complete finite eons. Finite or infinite discrete populations are
  represented, with each eon's tick set finite. The rule about readings is
  stated as a model input; it is not asserted as a theorem about every Banach
  space.
  Generalized to `H(3+1+k)` (three axes, `q`, and `k` further independent
  observables). Thermal route: a nonzero thick forces the torus and `d ≥ 4`
  (`sin_cero_absoluto_abre_ruptura`, via `D20`/`D21`). Closing statement
  `distincion_cancela_cero_e_infinito`: in `H3` without distinction absolute
  zero is admissible; once B is distinguished from A, for every `k` the thick
  at `d = 3+1+k` is `δ_geom(d)`, positive, finite and inside the `D31` band. (ℝ⁴ euclidean is at once a Hilbert and a Banach space, so the Banach and
  Hilbert forms are the same theorem at two levels of generality.)
* `D36_SeedYRegistroH4`: `d = 3` has no quantum (`δ(3) = 0`, Robertson saturates),
  so smoothness without a quantum is possible *mathematically* in `d = 3`; but no
  open-eon record lives in `d = 3` (`d3_satura_pero_no_se_registra`). In `H₄` the
  saturation is impossible: RS is strict at every maximal-tension state, `δ(4) > 0` is
  the minimum over every open dimension and `δ_∞ > 0`
  (`suavidad_sin_cuanto_imposible_en_H4`). Hypotheses in view: the rupture postulate
  of `D34` and the `H₃ + q = H₄` rule of `D35`.
-/
