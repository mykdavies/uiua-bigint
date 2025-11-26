# ---BigInt ~ Add Big BigS Cmp Even Fact Fib Mul Odd One Sub Zero
# A BigInt is a decimal little-endian array preceeded by a sign digit
# [0] = zero, [-ve . . .] = negative [+ve ...] positive

One    ← [1 1]
Zero   ← [0]
NegOne ← [¯1 1]
Inf    ← [∞]
NegInf ← [¯∞]
IsOdd  ← ⨬(◿2⊡1|⋅0)⊸(≍Zero)
IsEven ← ¬ IsOdd
# Remove leading zeros
Nub ← ⍥(⋅[0])⊸(≍[])⍜⇌(↘˜⨂0⊸=₀)
# Negate
Neg ← ⍜⊢¯
# int <-> BigInt
Big ← ⌅(
  ⊂⊃(±|⇌≡⋕°⋕⌵)
| ×⊃(⊢|/(+×10)⇌↘1))
# String <-> BigInt
BigS ← ⌅(
  ⨬(⊂1⇌≡⋕|⊂¯1⇌≡⋕↘1)=@-⊸⊢
| ⍥(⊂@-)=¯1⊃(⊢|+@0⇌↘₁)
)
# Ensure we're getting a BigInt, not a plain int.
Coerce ↚ ⍥Big=0⧻⊸△

CmpBare ↚ ⊢▽⊸≠0⇌±⬚0-
# -1/0/1 ? a b - neg if a<b, pos if a>b, 0 if a=b
Cmp ← (
  ∩Coerce
  ⊟◡∩⊢ # take sign digits.
  ⍣(CmpBare ∩↘₁ °[1 1]
  | ¯CmpBare∩↘₁ °[¯1 ¯1]
  | ±/-
  )
)
Lt ← =¯1Cmp
Eq ← =0Cmp
Gt ← =1Cmp
Ge ← ¬Lt
Le ← ¬ Gt
Ne ← ¬ Eq

Abs ← ⍜⊢⌵

# Add two (sign-free) BigInts, handling large carries.
AddBare ↚ |2 Nub⍥(AddBare ⊃(⊂0⌊÷10|◿10))>0/↥⊸≥₁₀⬚0+
# Sub two (sign-free) BigInts (smaller first), handling borrows.
SubBare ↚ |2 (
  ⬚0-
  ⍢(⬚0+⬚0+⊃(⊂0|×¯10)×⊸<₀⌊⊸÷₁₀
  | /↥<0)
  Nub
)

# Ensure we take the smaller from the larger.
# signs n1 n2 -> sum.
SubHelp ↚ (
  ◡(≍Neg)
  ⨬(⊂⊙SubBare⍥(¯1◌⊙⊃⋅∘∘)⊸<₀◡CmpBare ∩↘₁
  | Zero)
)
# Finds appropriate action based on signs and magnitudes of numbers.
AddOrSub ↚ (
  ⊟◡∩⊢          # Take sign digits
  ⍣(◌◌ °(⊂0)    # Add 0 -> b
  | ⊙◌◌ ⍜⇌°(⊂0) # Add ... 0 -> a
  | ⊂ 1 AddBare ∩(↘1) °[1 1]
  | ⊂¯1 AddBare ∩(↘1) °[¯1 ¯1]
  | SubHelp °[¯1 1]
  | SubHelp ⊃⋅∘∘∩Neg °[1 ¯1]
  | "Error"
  )
)
Add ← AddOrSub∩Coerce
Sub ← Add Neg∩Coerce

Mul′ ↚ (
  ∩↘₁              # Drop (positive) signs.
  ⊙¤⍉⊟°⊏∩(˜⊂0)     # Build up mult table.
  ≡(□⊂⊃(˜↯0|⋅×)°⊟) # Do the raw multiplications.
  /◇AddBare        # Add them (also handles all the carries).
  ⊂1               # Restore positive signs.
)

# Multiply. Mul Zero Inf Eq Zero :-)
Mul ← (
  ∩Coerce
  ⍣(⋅Zero °1(≍Zero)
  | Zero °1(≍Zero◌)
  | ⋅Inf °1(≍Inf)
  | Inf °1(≍Inf◌)
  | Nub⍜⊢⋅∘⊃(Mul′∩⍜⊢⋅1|×∩⊢))
)

# b mod a - scales for very large numbers.
Mod ← Nub◌⍢(⟜(Sub⊂1↘2⍢(Mul10|Gt))|Gt) ∩Coerce

# Do the core division. Slow for very different numbers.
BaseDiv ↚ Coerce◌◌⍢(⊙⊙+₁⟜Sub|Ge) ⊙⊙0 ∩Coerce
Div₁₀   ↚ ⍥(⋅[0])=1⊸⧻⍜°⊂⊙↘₁
Mul₁₀   ↚ ⍜°⊂⊙(⊂0)

# Find biggest remaining scaled division.
Div′ ↚ (
  ⍢(⊙⊙Mul₁₀Mul₁₀|Gt)⊙⊙One
  Mul BaseDiv⊙⊙(Div₁₀)Div₁₀
)

# Repeat apply Div', summing results. i.e. Long division :-)
PosDiv ↚ (
  0
  ⍢(⊙(◡Div′)
    ⊃(Add|⋅⋅∘|Sub Mul◌)
  | ⋅Ge)
  ⊙(◌◌)
)

# remove and multiply signs, do PosDiv, re-apply sign.
Div ← (
  ∩Coerce
  ⍣(⋅Inf °1(≍Zero)
  | ⋅Zero °1(≍Inf)
  | Zero °1(≍Zero◌)
  | Inf °1(≍Inf◌)
  | Nub⍜⊢⋅∘⊃(PosDiv∩⍜⊢⋅1|×∩⊢))
)
# base exponent
Pow ← ⍥Mul⊙(⟜∘)-1°Big∩Coerce
# This kinda works, but is pointless as it gives too many
# multiplications for large exponents. Need an iterative approach.
# e.g. 'Addition-chain exponentiation'
# Pow ← ⊙◌◌⍢(Sub One⊙⊸Mul|Lt Zero) Sub One⊙(⟜∘)∩Coerce

Gcd ← ◌⍢(⤙˜Mod|Ne) ∩Coerce
Lcm ← Div⊃(Gcd|Abs Mul)∩Coerce

Fib′ ↚ |1 memo(⨬(Add ⊃(Fib′ Sub One|Fib′ Sub[1 2])|One)<1⊸Cmp[1 2])
Fib  ← |1 Fib′Coerce

Fact ← |1 ⨬(Mul Fact⊸Sub One|⋅One)<0⊸Cmp[1 2]Coerce

┌─╴test
  ⍤⤙≍ [¯1 0 1] Big ¯10
  ⍤⤙≍ ¯10 °Big [¯1 0 1]
  ⍤⤙≍ [¯1 0 1] BigS "-10"
  ⍤⤙≍ "-10" °BigS [¯1 0 1]

  ⍤⤙≍ 1 IsOdd [1 1 1]
  ⍤⤙≍ 1 IsEven [¯1 0 1]
  ⍤⤙≍ 1 CmpBare [1 1] [2 1]
  ⍤⤙≍ ¯1 CmpBare [2 1] [9]
  ⍤⤙≍ 1 CmpBare [9] [2 1]
  ⍤⤙≍ 1 Cmp [1 1 1] [1 2 1]
  ⍤⤙≍ ¯1 Cmp [1 2 1] [1 9]
  ⍤⤙≍ 1 Cmp [1 9] [1 2 1]
  ⍤⤙≍ 1 Cmp [1 1 1] [1 1 2]
  ⍤⤙≍ ¯1 Cmp [1 1 1] [¯1 1 2]
  ⍤⤙≍ ¯1 Cmp [1 1 1] [0]
  ⍤⤙≍1 Cmp [¯1 1] [1 2]

  ⍤⤙≍ [0] Nub [0 0]
  ⍤⤙≍ [0 1] Nub [0 1]
  ⍤⤙≍ [1 4] AddBare [0 1] [1 3]
  ⍤⤙≍ [0 5] AddBare [9 1] [1 3]
  ⍤⤙≍ [1 4] Add One [1 3]
  ⍤⤙≍ [1 4] Add One 3
  ⍤⤙≍ [1 1 5] Add Big 12 Big 39
  ⍤⤙≍ [2 7] SubBare [1 2] [3 9]
  ⍤⤙≍ [3] SubBare [9 1] [2 2]
  ⍤⤙≍ [1 7 2] Add Big ¯12 Big 39

  ⍤⤙≍ [1 2] Add [¯1 1] [1 3]
  ⍤⤙≍ [1 2] Sub One [1 3]
  ⍤⤙≍ [0] Sub One One
  ⍤⤙≍ [¯1 2] Sub [1 3] [1 1]

  ⍤⤙≍ [1 2 3] Add [1 2 3] [0]
  ⍤⤙≍ [1 2 3] Add [0] [1 2 3]
  ⍤⤙≍ [1 2 4] Add[1 2 1][1 20 1]

  ⍤⤙≍ [¯1 2 3] Sub [1 2 3] [0]
  ⍤⤙≍ [1 2 3] Sub [0] [1 2 3]
  ⍤⤙≍ [1 3 3] Add [1 1] [1 2 3]
  ⍤⤙≍ [1 3 3] Sub [¯1 1] [1 2 3]
  ⍤⤙≍ [1 2] Add [¯1 1] [1 3]
  ⍤⤙≍ [1 2] Sub [1 1] [1 3]
  ⍤⤙≍ [¯1 3 3] Sub [1 1] [¯1 2 3]
  ⍤⤙≍ [¯1 1 3] Add [1 1][¯1 2 3]
  ⍤⤙≍ [¯1 1 3] Add [¯1 2 3][1 1]
  ⍤⤙≍ ¯100 °Big Mul[¯1 5][1 0 2]
  ⍤⤙≍ 0 °Big Mul[0][1 0 2]
  VeryBig ← [1 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
  Add [1 1] Mul VeryBig[1 0 0 0 0 0 0 2]
  ⍤⤙≍ [1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]

  ⍤⤙≍ 1 °Big Mod 3 100
  ⍤⤙≍ 1 °Big Mod 3 VeryBig

  ⍤⤙≍ 4 °Big Div[1 5][1 0 2]
  ⍤⤙≍ ¯4 °Big Div[¯1 5][1 0 2]
  ⍤⤙≍ ¯4 °Big Div[1 5][¯1 0 2]
  ⍤⤙≍ 4 °Big Div[¯ 1 5][¯1 0 2]
  ⍤⤙≍ 400000000 °Big Div[1 5][1 0 0 0 0 0 0 0 0 0 2]

  ⍤⤙≍ 8 °Big Fib Big 6
  ⍤⤙≍ 120 °Big Fact Big 5
  ⍤⤙≍ 210 °Big Lcm 14 15
└─╴
