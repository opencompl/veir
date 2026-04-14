window.BENCHMARK_DATA = {
  "lastUpdate": 1776204989494,
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
          "id": "3cd5db45bce96e4a5be17772ba457352967c64ec",
          "message": "Increase CI benchmark alert-threshold to 500% (#411)\n\nOur benchmarks are currently very noisy. Let's move the noise threashold\nup to avoid continious failing benchmark runs in CI.",
          "timestamp": "2026-04-13T10:25:34Z",
          "tree_id": "7e156c670d587a8f68beed63e30b80241e1a4e13",
          "url": "https://github.com/opencompl/veir/commit/3cd5db45bce96e4a5be17772ba457352967c64ec"
        },
        "date": 1776076068782,
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
            "value": 3236000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003236s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2281000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002281s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2679000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002679s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2257000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002257s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2156000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002156s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1828000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001828s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1788000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001788s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2244000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002244s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4591000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.004591s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2232000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002232s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2643000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002643s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2222000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002222s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1806000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001806s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1822000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001822s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1423000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001423s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2212000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002212s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3163000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003163s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1829000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001829s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 10000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000010s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1859000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001859s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 768000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000768s"
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
          "id": "11fadf749025247a7dadbbed248536e735bd88fe",
          "message": "Add `createBlock` and `insertBlock` to the `PatternRewriter` (#412)\n\nThese were missing from the pattern rewriter, and are needed for the\nriscv backend.",
          "timestamp": "2026-04-13T10:47:51Z",
          "tree_id": "975e1b13923694d94d9161ae79caf505df684fe8",
          "url": "https://github.com/opencompl/veir/commit/11fadf749025247a7dadbbed248536e735bd88fe"
        },
        "date": 1776077422936,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1875000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001875s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3474000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003474s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1890000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001890s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2814000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002814s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1857000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001857s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2199000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002199s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1573000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001573s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1736000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001736s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1901000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001901s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4849000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.004849s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1868000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001868s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2719000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002719s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1853000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001853s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1717000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001717s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1609000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001609s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1388000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001388s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1858000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001858s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3230000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003230s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1617000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001617s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1570000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001570s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 740000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000740s"
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
          "id": "73b4e09349c311271e91da7a7ee2d4291601e812",
          "message": "Move HasDialectOpInfo into dialect-specific files (#410)\n\nThis PR moves the Op to properties mapping to dialect-specific files.\nThis gently leads towards increasingly more per-dialect definitions.\n\nThis Pr does not change functionality beyond moving definitions around.",
          "timestamp": "2026-04-13T10:51:29Z",
          "tree_id": "09a473d8d3340a5f7e234daf5e740b14acf3827e",
          "url": "https://github.com/opencompl/veir/commit/73b4e09349c311271e91da7a7ee2d4291601e812"
        },
        "date": 1776077714123,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2297000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002297s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3798000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003798s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2471000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002471s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3072000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003072s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2172000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002172s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2443000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002443s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2074000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002074s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2004000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002004s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2396000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002396s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5348000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005348s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2333000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002333s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3026000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003026s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2130000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002130s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2010000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002010s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1905000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001905s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1560000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001560s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2449000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002449s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3807000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003807s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2071000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002071s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1987000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001987s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 779000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000779s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "48860705+luisacicolini@users.noreply.github.com",
            "name": "Luisa Cicolini",
            "username": "luisacicolini"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "4ae8ad8fd7bb37199d763ba596c540bbfcc3e279",
          "message": "refinement relation from `LLVM.Int` to `RISCV.Reg` (#414)\n\nWe add the definition of the refinement relation from `LLVM.Int` to\n`RISCV.Reg`. This is the core relation we want to reason about when\nproving the correctness of instruction selection patterns. We say an\ninteger `i : LLVM.Int` is refined by a register `r : RISCV.Reg` if the\nbehaviours allowed by the register are a subset smaller or equal to the\ninteger's behaviour.\n\nFormally, an integer `i : LLVM.Int` is refined by a register `r :\nRISCV.Reg` iff:\n* if `i` is a concrete value `.val v`, then the register `r` must\ncontain `v` (i.e., `r.val = v`), and the two behave identically.\n* if `i` is a `.poison`, any value can refine it and the relation always\nholds, as the register displays a specific behaviour among the different\nones `poison` can have.",
          "timestamp": "2026-04-13T20:32:35Z",
          "tree_id": "46c589a66f455c412474313a5218d6f5144aa306",
          "url": "https://github.com/opencompl/veir/commit/4ae8ad8fd7bb37199d763ba596c540bbfcc3e279"
        },
        "date": 1776112489468,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2391000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002391s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3711000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003711s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2194000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002194s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3112000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003112s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2094000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002094s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2458000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002458s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1838000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001838s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1978000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001978s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2405000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002405s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5275000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005275s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2170000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002170s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3111000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003111s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2400000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002400s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2012000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002012s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1950000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001950s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1555000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001555s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2168000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002168s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3634000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003634s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2046000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002046s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1716000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001716s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 799000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000799s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "48860705+luisacicolini@users.noreply.github.com",
            "name": "Luisa Cicolini",
            "username": "luisacicolini"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "7b7f813fef042d97440968d547b63b8aa75d76d3",
          "message": "llvm: `constant` semantics (#415)\n\nWe add explicit, declarative semantics of `llvm.constant` operation.\nThis is useful to reason about the correctness of rewrites, e.g. in the\ncontext of instruction selection. The semantics are unchanged in\npractice, but wrapped in their own deifnition just like every other\noperation.\n\n---------\n\nCo-authored-by: Mathieu Fehr <mathieu.fehr@gmail.com>",
          "timestamp": "2026-04-13T21:15:43Z",
          "tree_id": "0105cef5191136de7da64240574f81861cfbce87",
          "url": "https://github.com/opencompl/veir/commit/7b7f813fef042d97440968d547b63b8aa75d76d3"
        },
        "date": 1776115101819,
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
            "value": 3794000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003794s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2122000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002122s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3119000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003119s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2399000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002399s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2429000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002429s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1874000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001874s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1996000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001996s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2510000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002510s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5327000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005327s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2406000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002406s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3023000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003023s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2234000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002234s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1948000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001948s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2112000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002112s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1594000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001594s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2361000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002361s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3667000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003667s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1966000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001966s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2087000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002087s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 772000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000772s"
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
          "id": "c2650f2953845729f5c97c773d226e12bfa279e4",
          "message": "Modularize the `Rewriter.WellFormed` directory (#396)",
          "timestamp": "2026-04-13T21:24:48Z",
          "tree_id": "cf9802e2800ecbbfbec4a5f802b4509c2e350cf6",
          "url": "https://github.com/opencompl/veir/commit/c2650f2953845729f5c97c773d226e12bfa279e4"
        },
        "date": 1776115895182,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2150000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002150s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3796000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003796s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2314000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002314s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3162000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003162s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2415000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002415s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2444000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002444s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2058000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002058s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2125000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002125s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2573000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002573s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5355000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005355s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2111000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002111s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3060000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003060s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2448000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002448s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2021000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002021s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1980000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001980s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1555000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001555s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2445000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002445s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3719000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003719s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1960000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001960s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1907000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001907s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 766000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000766s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "48860705+luisacicolini@users.noreply.github.com",
            "name": "Luisa Cicolini",
            "username": "luisacicolini"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "969aa4564526a3cc4b67589088e1eabbc4ffaeb7",
          "message": "instruction selection: `constant`, `add` refinement proof (#416)\n\nWe prove the correctness of the lowering pattern for `constant` and\n`add`. If we agree on this format and organization I will write more\nproofs and push them. Note that the proof for `constant` does not deal\nwith `.poison`, as `llvm.constant` is never poison.\n\nI think we have two options to consider wrt. lemmas' formulation: \n* wrapping the semantics of the `unrealized_conversion_cast`\n(i.e.,`toReg : i64 -> !reg`) directly in the lemma and proving the\nrefinement `i64` to `!reg`.\n* wrapping the semantics of the `unrealized_conversion_cast` *in both\ndirections* (i.e.,`toReg : i64 -> !reg` and `toInt : !reg -> i64`). This\nwould be more consistent with what the rewriter actually does, and the\nrefinement goes from `i64` to `i64`.\n\nI am pushing both option and look forward to gathering opinions :)\n\nAlso, the tactic is the usual:\n* unwrap semantics\n* split + get rid of monad\n* `bv_decide`\n\nIf we agree on these steps we can wrap it into an actual tactic, as we\ndid in `lean-MLIR` (for a subsequent PR).",
          "timestamp": "2026-04-14T13:46:39Z",
          "tree_id": "b069d00f97f4c975bc6184e8176cb404acea98fe",
          "url": "https://github.com/opencompl/veir/commit/969aa4564526a3cc4b67589088e1eabbc4ffaeb7"
        },
        "date": 1776174551012,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2416000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002416s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3727000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003727s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2391000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002391s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3146000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003146s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2297000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002297s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2429000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002429s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1973000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001973s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2017000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002017s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2378000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002378s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5528000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005528s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2385000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002385s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3055000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003055s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2339000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002339s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1988000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001988s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1895000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001895s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1600000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001600s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2330000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002330s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3654000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003654s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2032000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002032s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1981000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001981s"
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
          "distinct": false,
          "id": "19c4485ae215d39703bf93a0a049ba5fb6d5773d",
          "message": "nightly-2026-04-14 lean nightly update (#419)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-04-14T15:18:33Z",
          "tree_id": "c10e937d400b0afd4b843943b27674af997ecc3f",
          "url": "https://github.com/opencompl/veir/commit/19c4485ae215d39703bf93a0a049ba5fb6d5773d"
        },
        "date": 1776180053433,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2166000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002166s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3869000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003869s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2269000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002269s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3185000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003185s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2171000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002171s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2492000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002492s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2199000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002199s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1989000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001989s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2814000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002814s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5284000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005284s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2473000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002473s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3156000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003156s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2486000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002486s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1944000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001944s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2203000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002203s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1593000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001593s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2611000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002611s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3730000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003730s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2229000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002229s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2099000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002099s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 793000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000793s"
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
          "id": "38c30fdf92e61baed8cbaec9160b71e356eb9108",
          "message": "[ci] Fix noise in benchmarks  (#413)\n\nEach benchmark ran once which produced highly variable results.\n\n  ## Fix \n1. .github/scripts/run_benchmarks.sh — Run each benchmark 5 times and\nreport the median\n  2. .github/workflows/ci.yml: \n    - Pass 5 as the iterations argument: run_benchmarks.sh 1000 100 5\n- Increase threshold to a very large value, effectively disabling\nalerts.",
          "timestamp": "2026-04-14T17:00:46Z",
          "tree_id": "a5b921ce5ab2825328e7418a10c89016ba2c041c",
          "url": "https://github.com/opencompl/veir/commit/38c30fdf92e61baed8cbaec9160b71e356eb9108"
        },
        "date": 1776186192747,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2165000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002165s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3747000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003747s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2259000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002259s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3144000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003144s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2305000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002305s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2408000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002408s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1918000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001918s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1919000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001919s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2208000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002208s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5269000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005269s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2155000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002155s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3069000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003069s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2314000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002314s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1999000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001999s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1894000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001894s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1549000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001549s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2309000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002309s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3672000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003672s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1945000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001945s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1867000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001867s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 781000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000781s"
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
          "id": "87484c652bea46b53799e19adc43ab7685f37a03",
          "message": "increase maxHeartbeats for doc build (#420)",
          "timestamp": "2026-04-14T22:13:59Z",
          "tree_id": "1a00282e1e335ad8c087df83c4ae166a407e4942",
          "url": "https://github.com/opencompl/veir/commit/87484c652bea46b53799e19adc43ab7685f37a03"
        },
        "date": 1776204985357,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2119000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002119s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3213000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003213s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2098000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002098s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2680000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002680s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2124000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002124s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2138000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002138s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1720000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001720s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1752000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001752s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2108000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002108s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4546000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004546s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2103000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002103s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2596000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002596s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2107000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002107s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1736000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001736s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1745000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001745s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1391000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001391s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2102000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002102s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3119000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003119s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1706000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001706s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1730000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001730s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 727000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000727s"
          }
        ]
      }
    ]
  }
}