# Release checklist for the stated fragment

- [ ] Pin Lean 4.32.0 with `lean-toolchain` and a minimal Lake project.
- [ ] Split the cone route from retired machinery and enable `set_option autoImplicit false`.
- [ ] Add capstone `#print axioms` declarations and an exact allowlist transcript.
- [ ] Rebuild twice in independent clean environments and retain logs/metadata.
- [ ] Prove the complete abstract-to-region semantics and satisfaction bridge.
- [ ] Add raw syntax, NNF/inverse normalization, and semantic preservation.
- [ ] Prove the explicit signature and complexity bounds.
- [ ] Export a reflected Boolean core and a three-valued out-of-scope/unknown wrapper.
- [ ] Test generated code and audit executable dependencies.
- [ ] Port all prescribed regressions into Lean.
- [ ] Repair or reclassify `wp133` so the green release gate exits 0.
- [ ] Generate the theorem manifest, checksums, build logs, and a fail-closed release script.

This audit package supplies checksums and a safe wrapper for the current inputs. It does
not mark the unchecked items above as completed.
