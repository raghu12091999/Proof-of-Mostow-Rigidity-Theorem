/-- The similarity map `(z,t) ↦ (a*z + b, |a|*t)` on H3, for `a ≠ 0`. -/
def similarity (a b : ℂ) (ha : a ≠ 0) : H3 → H3 :=
  fun p => mk (a * p.z + b) (‖a‖ * p.t) (by
    have := p.t_pos
    have habs : 0 < ‖a‖ := by simpa using ha
    positivity)

/-- **F1.** When `a ≠ 0`, the map `(z,t) ↦ (az+b, |a|t)` acts isometrically on H3. -/
theorem F1_isometry (a b : ℂ) (ha : a ≠ 0) (p q : H3) :
    dist (similarity a b ha p) (similarity a b ha q) = dist p q := by
  unfold dist coshArg similarity
  simp only [mk_z, mk_t]
  congr 1
  have habs : 0 < ‖a‖ := by simpa using ha
  have hp := p.t_pos
  have hq := q.t_pos
  have hdiff : a * p.z + b - (a * q.z + b) = a * (p.z - q.z) := by ring
  rw [hdiff, norm_mul]
  field_simp [habs.ne', hp.ne', hq.ne']
