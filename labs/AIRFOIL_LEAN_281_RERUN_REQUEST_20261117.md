# INSACERMO AIRFOIL — exact 281-row Lean rerun request (2026-11-17)

Purpose: submit a fresh push to test the **corrected** Lean proof generator,
not the stale diagnostic from before commit e12fb884242abb1b6f1eec16a2da286d3f895987.

Historical INSACERMO/C3 sources unchanged. Sealed model and original airfoil
physical dataset unchanged. No threshold adjustment.

Previous independent 281-row numerical generator exit=0:
- upper model SSE (thousandth-dB squared): 4771789349
- lower baseline SSE (thousandth-dB squared): 6254654607
- 5 dB RMS gate: 4771789349 < 25*281*1000000 = 7025000000
- 10% RMS reduction gate: 100*4771789349 = 477178934900 < 81*6254654607 = 506627023167
- minimum improvement under reported outward rounding: 12.654815679699205%.
- source data SHA256: 10ee06e6cfb27dae6b44213d421d217012fb1f9b697592e73a4e4016b52d425f

Old Lean error: unknown identifier `lt_of_le_of_lt` on row 351.
Code corrected by using a `calc` transitivity proof instead. The GitHub
diagnostic remains stale until a new generated certificate is compiled.

Only call this a successful **281-row Lean** proof when the workflow publishes
`labs/airfoil_rowwise_lean_receipts_20261117/Airfoil281RowCertificate.lean`
and corresponding `rowwise_receipt.json`, or the latest `status.txt`
shows generator_exit=0, lean_exit=0, result=PASS.
