import Magma.AdequacyStoreKit

/-!
# Adequacy campaign, rung 6 (entry): the general entry lemma

One kernel fact: from the `meval` wrapper body with *any* argument
bound over *any* initial environment's artifacts, 17 steps reach
the calling convention — the ρ₀-general form of the startup rung's
`call_entry`. Rung 6's tower construction needs it because the
tower program evaluates META from the *empty* environment, not from
`[⌜p⌝]`: the wrapper is entered with the argument produced by an
ordinary application, and this lemma carries it into `mevalCallS`.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyEntry

open FactorizationEqv MetaImage AdequacyStartup AdequacyStoreKit

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
/-- **The general entry**: the wrapper body over any `ρ₀`'s
    artifacts, any bound argument, any continuation — 17 steps to
    the calling convention with the empty suffix. -/
theorem entry17 (ρ₀ : Env) (arg : Val) (κ : Kont) :
    stepIter 17 (.eval metaBody (arg :: metaEnvF ρ₀)
        (knotStoreF ρ₀) κ) =
      .inl (mevalCallS ρ₀ [] arg (.elem 0) κ) :=
  rfl

end AdequacyEntry
end Dichotomic
