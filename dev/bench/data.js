window.BENCHMARK_DATA = {
  "lastUpdate": 1776072402974,
  "repoUrl": "https://github.com/opencompl/veir",
  "entries": {
    "VeIR Benchmarks": [
      {
        "commit": {
          "author": {
            "email": "70980689+snarang181@users.noreply.github.com",
            "name": "Samarth Narang",
            "username": "snarang181"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "8f1a472f4c8a70bbb7b438baf0388c6acc767eff",
          "message": "Add benchmark profiling and regression tracking to (#350)\n\n## Summary                                                             \n- Add a new CI workflow that runs all 11 rewrite benchmarks on every\n  push to `main` and on PRs \n- PRs that regress any benchmark by >10% will fail CI and get a comment\n   with the comparison",
          "timestamp": "2026-04-11T18:43:02Z",
          "tree_id": "a31d8808376701efcba809261b6a069e77eafd53",
          "url": "https://github.com/opencompl/veir/commit/8f1a472f4c8a70bbb7b438baf0388c6acc767eff"
        },
        "date": 1775933133516,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2244000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002244s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3708000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003708s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2324000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002324s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3061000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003061s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2261000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002261s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2516000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002516s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1755000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001755s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1983000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001983s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2329000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002329s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5261000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005261s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2265000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002265s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3049000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003049s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2314000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002314s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1955000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001955s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1837000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001837s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1526000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001526s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2184000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002184s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3607000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003607s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1819000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001819s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1956000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001956s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 777000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000777s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "mathieu.fehr@gmail.com",
            "name": "Mathieu Fehr",
            "username": "math-fehr"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "cc082fa4bf96ecb6a644fab15945ed95de12ce46",
          "message": "Reduce proof time of `OpOperands.lean` (#397)",
          "timestamp": "2026-04-11T18:44:10Z",
          "tree_id": "f854d48a6e38def9103042a2dffe09dbaaea6550",
          "url": "https://github.com/opencompl/veir/commit/cc082fa4bf96ecb6a644fab15945ed95de12ce46"
        },
        "date": 1775933322199,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2137000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002137s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3703000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003703s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2361000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002361s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3172000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003172s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2356000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002356s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2461000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002461s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1814000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001814s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1947000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001947s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2175000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002175s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5279000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005279s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2378000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002378s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2976000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002976s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2205000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002205s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1962000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001962s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2059000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002059s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1533000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001533s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2259000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002259s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3555000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003555s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1889000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001889s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1954000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001954s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 785000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000785s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "tobias@grosser.es",
            "name": "Tobias Grosser",
            "username": "tobiasgrosser"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f265cbe909287e67c0b024e14d09c8483cd44e56",
          "message": "Add back maxHeartbeats to avoid timeout (#399)",
          "timestamp": "2026-04-11T19:00:21Z",
          "tree_id": "8a05496ab95648225ac17ab93c7989d67e5f7f1d",
          "url": "https://github.com/opencompl/veir/commit/f265cbe909287e67c0b024e14d09c8483cd44e56"
        },
        "date": 1775934294918,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1907000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001907s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3669000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003669s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1922000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001922s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2934000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002934s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1879000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001879s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2272000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002272s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1689000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001689s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1916000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001916s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1874000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001874s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5056000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005056s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2164000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002164s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2782000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002782s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1897000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001897s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1768000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001768s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1629000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001629s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1432000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001432s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2010000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002010s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3568000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003568s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1590000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001590s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1599000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001599s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 812000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000812s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "tobias@grosser.es",
            "name": "Tobias Grosser",
            "username": "tobiasgrosser"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "5dfc20d645fc3a21e1d4329aa5db0648d9bfa9eb",
          "message": "nightly-2026-04-11 lean nightly update (#400)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-04-12T15:07:14Z",
          "tree_id": "baec68d00893259a8a99c38c2939ef32dbe17d97",
          "url": "https://github.com/opencompl/veir/commit/5dfc20d645fc3a21e1d4329aa5db0648d9bfa9eb"
        },
        "date": 1776006560336,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2641000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002641s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 4671000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.004671s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1851000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001851s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2950000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002950s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1852000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001852s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2280000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002280s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1536000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001536s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1757000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001757s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1833000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001833s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4744000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.004744s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1793000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001793s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2688000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002688s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1829000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001829s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1746000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001746s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1576000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001576s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1365000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001365s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1826000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001826s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3223000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003223s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1765000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001765s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1591000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001591s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 754000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000754s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "tobias@grosser.es",
            "name": "Tobias Grosser",
            "username": "tobiasgrosser"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "6a1ff21de75a8be5daba2549e08ef9b4921b1243",
          "message": "factor propertiesOf into dialect-specific functions (#392)\n\nThis is a first step towards making a our dialect definitions more\nmodular.",
          "timestamp": "2026-04-12T21:42:50Z",
          "tree_id": "0cf7814145cbb8a99025e687ec41ce2b171ab521",
          "url": "https://github.com/opencompl/veir/commit/6a1ff21de75a8be5daba2549e08ef9b4921b1243"
        },
        "date": 1776031058275,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1856000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001856s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3466000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003466s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1907000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001907s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2896000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002896s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1856000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001856s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2145000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002145s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1557000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001557s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1788000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001788s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1870000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001870s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4903000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.004903s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2212000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002212s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2724000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002724s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1856000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001856s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1733000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001733s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1671000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001671s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1552000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001552s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1876000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001876s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3262000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003262s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1588000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001588s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 10000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000010s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1567000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001567s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 743000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000743s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "70980689+snarang181@users.noreply.github.com",
            "name": "Samarth Narang",
            "username": "snarang181"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "8bb9748b4b66d7a7a76651f0293570e291e4f133",
          "message": "Merge benchmarks and docs in a single CI workflow (#402)\n\n## Current Issue\n- opencompl.github.io/veir/dev/bench/ returns 404 because the docs\ndeployment (deploy-pages@v4) overwrites the benchmark pages that\nbenchmark-action pushes to gh-pages\n\n## Summary of PR\n\n- Merges benchmarks.yml and build_docs.yml into a single ci.yml with 3\njobs: benchmark, build-docs, and deploy\n- The deploy job checks out gh-pages (with fresh benchmark data),\noverlays docs on top preserving dev/, and pushes once so both docs and\nbenchmarks are served from the same branch\n- After merge to main, opencompl.github.io/veir/ serves docs and\nopencompl.github.io/veir/dev/bench/ serves benchmark charts",
          "timestamp": "2026-04-13T04:39:37Z",
          "tree_id": "1abe8c8043293f644618621bc0e8256fedabbb1f",
          "url": "https://github.com/opencompl/veir/commit/8bb9748b4b66d7a7a76651f0293570e291e4f133"
        },
        "date": 1776055313172,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2254000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002254s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3691000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003691s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2073000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002073s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3104000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003104s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2125000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002125s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2396000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002396s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1809000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001809s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1951000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001951s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2118000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002118s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5254000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005254s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2223000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002223s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2981000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002981s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2362000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002362s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1971000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001971s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1831000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001831s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1566000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001566s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2288000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002288s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3651000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003651s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1905000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001905s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1851000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001851s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 748000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000748s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "70980689+snarang181@users.noreply.github.com",
            "name": "Samarth Narang",
            "username": "snarang181"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "15bb3d6af0f5e67d89a8c4d85d7bd6e4d1d82826",
          "message": "Add nightly CI for veir-tests (#403)\n\nAdd a GitHub Actions workflow that runs differential tests from\nveir-tests nightly.",
          "timestamp": "2026-04-13T04:53:30Z",
          "tree_id": "c7b647698f4726c6f77d89f71dedc829503a7024",
          "url": "https://github.com/opencompl/veir/commit/15bb3d6af0f5e67d89a8c4d85d7bd6e4d1d82826"
        },
        "date": 1776056139291,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2193000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002193s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3804000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003804s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2352000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002352s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3684000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003684s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2353000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002353s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2573000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002573s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1829000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001829s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1983000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001983s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2272000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002272s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5224000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005224s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2270000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002270s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3008000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003008s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2183000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002183s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1969000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001969s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1892000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001892s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1514000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001514s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2289000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002289s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3657000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003657s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1929000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001929s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1818000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001818s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 845000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000845s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "mathieu.fehr@gmail.com",
            "name": "Mathieu Fehr",
            "username": "math-fehr"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "7e957df67903a0f4f93282525e1b1356f990b308",
          "message": "Small Readme update (#401)",
          "timestamp": "2026-04-13T05:10:29Z",
          "tree_id": "0b8d3fab38cf701baeff496e7a6b9bac32e30ecd",
          "url": "https://github.com/opencompl/veir/commit/7e957df67903a0f4f93282525e1b1356f990b308"
        },
        "date": 1776057159993,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1982000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001982s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3460000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003460s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1857000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001857s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2935000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002935s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1916000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001916s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2205000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002205s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1562000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001562s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1759000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001759s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1873000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001873s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4780000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.004780s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1846000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001846s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2679000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002679s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2053000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002053s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1785000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001785s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1553000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001553s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1386000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001386s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1892000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001892s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3230000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003230s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1533000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001533s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1681000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001681s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 753000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000753s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "tobias@grosser.es",
            "name": "Tobias Grosser",
            "username": "tobiasgrosser"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "46a18b0da08831dfa2202269c75caf5072c3b72c",
          "message": "Enhance README with detailed VeIR features (#404)\n\nExpanded the description of VeIR and added a feature table with\ncompletion and verification status.",
          "timestamp": "2026-04-13T05:20:06Z",
          "tree_id": "1924fe96e52ea2bb773620bc29ce3f9dde9de177",
          "url": "https://github.com/opencompl/veir/commit/46a18b0da08831dfa2202269c75caf5072c3b72c"
        },
        "date": 1776057756663,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1465000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001465s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 2668000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002668s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1460000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001460s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2224000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002224s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1585000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001585s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 1723000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001723s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1237000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001237s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1401000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001401s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1453000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001453s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 3732000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003732s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1754000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001754s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2159000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002159s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1474000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001474s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1362000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001362s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1215000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001215s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1087000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001087s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1493000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001493s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 2555000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002555s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1334000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001334s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1225000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001225s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 585000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000585s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "tobias@grosser.es",
            "name": "Tobias Grosser",
            "username": "tobiasgrosser"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "09b9676a0968397452fa74c256a0bafdd4de80f8",
          "message": "Change comment-on-alert to false in CI workflow (#405)\n\nThis hides the benchmark noise we are currently seeing, e.g., in\nhttps://github.com/opencompl/veir/pull/401.",
          "timestamp": "2026-04-13T05:23:39Z",
          "tree_id": "a08d75e30755d1d4f2d84ad41a2a181161bdfe8a",
          "url": "https://github.com/opencompl/veir/commit/09b9676a0968397452fa74c256a0bafdd4de80f8"
        },
        "date": 1776057948186,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2458000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002458s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3794000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003794s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2186000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002186s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3118000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003118s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2392000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002392s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2495000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002495s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1932000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001932s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1985000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001985s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2288000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002288s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5300000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005300s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2262000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002262s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3125000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003125s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2166000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002166s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1981000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001981s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1959000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001959s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1535000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001535s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2167000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002167s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3670000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003670s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1855000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001855s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1926000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001926s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 776000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000776s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "tobias@grosser.es",
            "name": "Tobias Grosser",
            "username": "tobiasgrosser"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "638d300a522ba763bb7df42535642008e797718e",
          "message": "Fix formatting in README.md (#407)",
          "timestamp": "2026-04-13T05:26:41Z",
          "tree_id": "9408c3f5401499674b06b04cdda20e755df0e07c",
          "url": "https://github.com/opencompl/veir/commit/638d300a522ba763bb7df42535642008e797718e"
        },
        "date": 1776058117056,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2291000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002291s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3753000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003753s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2263000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002263s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3148000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003148s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2316000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002316s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2459000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002459s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1963000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001963s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2002000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002002s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2407000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002407s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5283000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005283s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2399000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002399s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3028000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003028s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2208000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002208s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1951000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001951s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2058000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002058s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1544000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001544s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2413000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002413s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3675000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003675s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1900000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001900s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1924000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001924s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 776000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000776s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "tobias@grosser.es",
            "name": "Tobias Grosser",
            "username": "tobiasgrosser"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "86232d985e0bc0bb663d6a343ac7d216e83bd3b3",
          "message": "Refactor README formatting (#408)\n\nReformat README for improved readability by dropping the explicit\nenumeration of `a` and `b`.",
          "timestamp": "2026-04-13T05:30:20Z",
          "tree_id": "8c164db9eaf3fa634032368382744d12c31958c2",
          "url": "https://github.com/opencompl/veir/commit/86232d985e0bc0bb663d6a343ac7d216e83bd3b3"
        },
        "date": 1776058345163,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2385000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002385s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3838000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003838s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2489000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002489s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3108000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003108s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2337000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002337s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2418000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002418s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2094000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002094s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1957000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001957s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2312000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002312s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5208000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005208s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2628000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002628s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3024000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003024s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2326000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002326s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1961000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001961s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1930000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001930s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1526000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001526s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2629000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002629s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3705000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003705s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2039000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002039s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2112000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002112s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 774000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000774s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "tobias@grosser.es",
            "name": "Tobias Grosser",
            "username": "tobiasgrosser"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "a4979efe7eef58f5545f9eab9af1ba3f45708b38",
          "message": "Refactor VeIR features section in README (#409)\n\nRemoved duplicate feature table and updated formatting.",
          "timestamp": "2026-04-13T05:42:01Z",
          "tree_id": "814b0ef901ca162fe68d46c47458a4a05462197a",
          "url": "https://github.com/opencompl/veir/commit/a4979efe7eef58f5545f9eab9af1ba3f45708b38"
        },
        "date": 1776059055588,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2138000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002138s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3712000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003712s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2225000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002225s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3101000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003101s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2144000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002144s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2377000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002377s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1865000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001865s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1959000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001959s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2293000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002293s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5279000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005279s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2307000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002307s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3000000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003000s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2231000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002231s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1946000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001946s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1973000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001973s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1578000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001578s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2138000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002138s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3596000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003596s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1899000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001899s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1827000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001827s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 765000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000765s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "git@gzgz.dev",
            "name": "Gavin Zhao",
            "username": "GZGavinZhao"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d381932339e1e99620bac81a174793f210c2bdc3",
          "message": "IRContext.default and IRContext.create proofs for parser (#384)\n\nDepends on #383.\n\nRequired by #222.\n\n---------\n\nCo-authored-by: Mathieu Fehr <fehr@Mathieus-MacBook-Air.local>",
          "timestamp": "2026-04-13T09:12:48Z",
          "tree_id": "de945d9e821f069f80c94ab21f94f7ccde8d6054",
          "url": "https://github.com/opencompl/veir/commit/d381932339e1e99620bac81a174793f210c2bdc3"
        },
        "date": 1776072400323,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2072000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002072s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3736000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003736s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2509000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002509s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3137000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003137s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2332000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002332s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2386000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002386s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1856000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001856s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1958000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001958s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2257000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002257s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5248000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005248s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2331000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002331s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3120000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003120s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2146000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002146s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1966000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001966s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1837000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001837s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1529000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001529s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2159000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002159s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3639000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003639s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1897000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001897s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1750000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001750s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 758000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000758s"
          }
        ]
      }
    ]
  }
}