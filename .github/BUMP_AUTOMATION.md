# Automated Mathlib bumps

Version bumps run nightly on the Lean VM through the privately operated
`lean-pool-automation` repository. That repository owns the controller, tests,
repair prompts, account selection and deployment configuration.

The controller preserves a full-history bump checkout, uses Codex subscription
accounts through `cx`, validates the existing build and quality gates, and opens
a draft content PR for review. Execution logs, credentials and operator
instructions are maintained privately with the automation.

GitHub-hosted runners no longer perform migrations. Normal required PR checks
continue to run on the resulting content changes.
