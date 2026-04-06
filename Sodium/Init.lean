universe u

structure Sodium (σ : Type u) where private new ::

@[extern "lean_sodium_init"]
opaque Sodium.sodium (σ : Type u) : IO (Sodium σ)
