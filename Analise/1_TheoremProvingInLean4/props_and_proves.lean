variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    ( -- p ∧ q → q ∧ p
      fun h : p ∧ q =>
      show q ∧ p from And.intro (And.right h) ( And.left h )
    )
    ( -- q ∧ p → p ∧ q
      fun h : q ∧ p =>
      show p ∧ q from And.intro (And.right h) (And.left h)
    )

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    ( -- p ∨ q → q ∨ p
      fun h : p ∨ q =>
      Or.elim h
        ( fun hp : p =>
            show q ∨ p from Or.intro_right q hp)
        ( fun hq : q =>
            show q ∨ p from Or.intro_left p hq)
    )

    (
      fun h : q ∨ p =>
      Or.elim h
        ( fun hq : q =>
            show p ∨ q from Or.intro_right p hq)
        ( fun hp : p =>
            show p ∨ q from Or.intro_left q hp )
    )


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (
      fun h : (p ∧ q) ∧ r =>
        show p ∧ (q ∧ r) from And.intro
          (And.left (And.left h))
          (And.intro (And.right (And.left h)) (And.right h) )
    )

    (
      fun h : p ∧ (q ∧ r) =>
        show (p ∧ q) ∧ r from And.intro
          (And.intro (And.left h) (And.left (And.right h)))
          (And.right (And.right h))
    )


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
  (
    fun h : (p ∨ q) ∨ r => Or.elim h
    (
      fun hpq : (p ∨ q) => Or.elim hpq
        (
          fun hp : p =>
            show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hp
        )
        (
          fun hq : q =>
            show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_left r hq)
        )
    )
    (
      fun hr : r =>
        show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_right q hr)
    )
  )
  (
    fun h : p ∨ (q ∨ r) => Or.elim h
    (
      fun hp : p =>
        show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_left q hp)
    )
    (
      fun hqr : (q ∨ r) => Or.elim hqr
      (
        fun hq : q =>
          show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_right p hq)
      )
      (
        fun hr : r =>
          show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) hr
      )
    )
  )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (
    fun h : p ∧ (q ∨ r) =>
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    Or.elim hqr
    (
      fun hq : q =>
        show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) (And.intro hp hq)
    )
    (
      fun hr : r =>
        show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) (And.intro hp hr)
    )
  )
  (
    fun h : (p ∧ q) ∨ (p ∧ r) =>
    Or.elim h
    (
      fun hpq : p ∧ q =>
      show p ∧ (q ∨ r) from And.intro hpq.left (Or.intro_left r (hpq.right))
    )
    (
      fun hpr : p ∧ r =>
      show p ∧ (q ∨ r) from And.intro hpr.left (Or.intro_right q (hpr.right))
    )
  )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  ( -- p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
    fun h : p ∨ (q ∧ r) =>
    Or.elim h
    (
      fun hp : p =>
      show (p ∨ q) ∧ (p ∨ r) from
        And.intro (Or.intro_left q hp) (Or.intro_left r hp)
    )
    (
      fun hqr : q ∧ r =>
      show (p ∨ q) ∧ (p ∨ r) from
        And.intro (Or.intro_right p hqr.left) (Or.intro_right p hqr.right)
    )
  )
  (
    fun h : (p ∨ q) ∧ (p ∨ r) =>
    have hpq : p ∨ q := h.left
    have hpr : p ∨ r := h.right
    Or.elim hpq
    (
      fun hp : p =>
      show p ∨ (q ∧ r) from
      Or.intro_left (q ∧ r) hp
    )
    (
      fun hq : q =>
      Or.elim hpr
      (
        fun hp : p =>
        show p ∨ (q ∧ r) from
        Or.intro_left (q ∧ r) hp
      )
      (
        fun hr : r =>
        show p ∨ (q ∧ r) from
        Or.intro_right p (And.intro hq hr)
      )
    )
  )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
  ( -- p → (q → r)
    fun h : p → ( q → r) =>
    fun hpq : p ∧ q =>
      have hp : p := hpq.left
      have hq : q := hpq.right
    show r from h hp hq
  )
  ( -- (p ∧ q ) → r
    fun h : (p ∧ q) → r =>
    fun hp : p =>
    fun hq : q =>
    show r from  h (And.intro hp hq)
  )

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  (
    fun h : (p ∨ q) → r =>
      And.intro
        ( fun hp : p => h (Or.inl hp))
        ( fun hq : q => h (Or.inr hq))
  )
  (
    fun h : (p → r) ∧ ( q → r )=>
    fun hpq : p ∨ q =>
    Or.elim hpq
      (fun hp : p => h.left hp)
      (fun hq : q => h.right hq)
  )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry

example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry

example : ¬(p ∧ ¬p) := sorry

example : p ∧ ¬q → ¬(p → q) := sorry

example : ¬p → (p → q) := sorry

example : (¬p ∨ q) → (p → q) := sorry

example : p ∨ False ↔ p := sorry

example : p ∧ False ↔ False := sorry

example : (p → q) → (¬q → ¬p) := sorry
