# Dependencies of the original Main proof

```mermaid
flowchart BT
  Counts["Actual completion / prescribed rank / row space"] --> J["Original finite probability bounds and uniform J"]
  List["Actual compatible lists / normalized Bayes decoding"] --> Graded["Actual Lüders rule / graded comparison"]
  J --> Converse["Original four uniform limits at zero and exact J bounds"]
  Graded --> Converse
  PGM["Actual normalized PGM on singular support"] --> Finite["Actual pointwise finite direct bounds"]
  Shell["Actual intersection bijection / exact shells / phase counts"] --> Finite
  Finite --> W["Fixed-W postprocessing for all inputs"]
  W --> Direct["Original four uniform limits at one under k−n→∞"]
  Converse --> Rate["Actual achievable witnesses and original liminf / sInf rates = 1"]
  Direct --> Rate
  Converse --> Main["Exact original Main proved"]
  Direct --> Main
  Rate --> Main
```

This is a reading guide. Actual dependencies are recorded in
[main-closure.json](validation/2026-10-11-direct-integration/main-closure.json)
and [lean-dependencies.json](lean-dependencies.json).
