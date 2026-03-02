# Copilot Instructions

## Response Style

- Provide succinct, focused responses
- Assume the user is a knowledgeable Lean expert
- Skip explanations of basic Lean concepts, syntax, or common error patterns
- Focus on the specific problem at hand rather than general tutorials

## Code Assistance

- Prefer direct solutions over step-by-step explanations
- When showing code examples, focus on the relevant parts
- Assume familiarity with Lean 4 syntax, tactics, and standard library

## PR Naming Convention

Follow the [mathlib commit style](https://leanprover-community.github.io/contribute/commit.html):

```
<kind>(<optional-scope>): <subject>
```

`<kind>` is one of: `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`, `ci`.

`<optional-scope>` is a module/directory path (e.g. `Data/Nat/Basic`), omitting any `Mathlib` prefix.

`<subject>`: lowercase first letter, no trailing dot, imperative present tense (e.g. "add" not "added").