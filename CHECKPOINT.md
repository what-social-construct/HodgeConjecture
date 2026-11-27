# Finite-point Gysin implementation checkpoint

This branch saves the current finite-point and affine-coordinate work before
continuing validation. The finite-point end-to-end build, focused controls,
proof-dependency audits, full integration and manuscript update are pending.
New finite-point claims in this checkpoint are draft scope, not a completed
validation report. Earlier verified checkpoints retain their recorded scope.

The pure `Topology/OnePointHomotopy.lean` compact-family theorem has passed its
focused Lean build (973 jobs). All 156 current import-boundary guards pass.
The affine production build is running under contention from other workspaces;
only one Hodge Lean job is active. Actual scheme charts, point-cycle leaves,
Gysin construction and certificate family remain queued for their checks.

The new certificate degree is GLOBAL square-cover rank at the selected target
point. It does not assert local multiplicity two at every finite point. The
push remains the earlier trace through the zero support. General proper trace,
nonlinear coordinate independence and infinity Gysin remain outside this work.

Next: finish the serialized checks, resolve any diagnostics, update the
manuscript and final validation records, then publish the verified result.
