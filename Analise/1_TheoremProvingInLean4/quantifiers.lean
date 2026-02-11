variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  ( -- (∀ x, p x ∧ q x)
    fun h: (∀ x, p x ∧ q x) =>
    show (∀ x, p x) ∧ (∀ x, q x) from And.intro (fun x => (h x).left) (fun x => (h x).right)
  )
  ( --(∀ x, p x) ∧ (∀ x, q x)
    fun h:(∀ x, p x) ∧ (∀ x, q x) =>
    show (∀ x, p x ∧ q x) from
      ( fun x => And.intro (h.left x) (h.right x))
  )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq : (∀ x, p x → q x) =>
  fun hp : (∀ x, p x) =>
  show (∀ x, q x) from
    (fun x => hpq x (hp x) )

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
  Or.elim h
  (
    fun hp : ∀ x , p x =>
    show ∀ x, p x ∨ q x from fun x => Or.intro_left (q x) (hp x)
  )
  (
    fun hq : ∀ x , q x =>
    show ∀ x , p x ∨ q x from
      fun x => Or.intro_right (p x) (hq x)
  )
