window.BENCHMARK_DATA = {
  "lastUpdate": 1778426304261,
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
          "id": "964db925aa78f1ce8377a693d92cf10d9e0b86b1",
          "message": "Move axioms to separate file (#422)\n\nThe doc builds currently fail with an error that axioms are not\npermitted in a module. Moving axioms to a separate file that is not a\nmodule fixes the doc build.\n\nThis PR also removes the previously introduced maxHeartBeats flag, which\nis not needed and has (for unknown reasons), no effect on the lean\nbuild. As the maxHeartBeats issues are only warnings, they do not affect\nthe docs build.",
          "timestamp": "2026-04-15T08:26:17Z",
          "tree_id": "cc40feba2e00a864169d77d9b19dd20dda67d53a",
          "url": "https://github.com/opencompl/veir/commit/964db925aa78f1ce8377a693d92cf10d9e0b86b1"
        },
        "date": 1776241837572,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2240000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002240s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3814000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003814s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2265000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002265s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3205000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003205s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2441000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002441s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2605000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002605s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2025000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002025s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2000000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002000s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2439000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002439s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5524000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005524s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2262000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002262s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3141000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003141s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2239000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002239s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2026000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002026s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1850000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001850s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1580000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001580s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2285000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002285s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3771000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003771s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1865000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001865s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1834000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001834s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 788000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000788s"
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
          "id": "ae72996df3ac403875a3366db40548f472955044",
          "message": "nightly-2026-04-16 lean nightly update (#423)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-04-16T15:23:02Z",
          "tree_id": "cbeea777e125fb14128a023be6f9aeb5568e9176",
          "url": "https://github.com/opencompl/veir/commit/ae72996df3ac403875a3366db40548f472955044"
        },
        "date": 1776353125337,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2104000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002104s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3223000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003223s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2110000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002110s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2690000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002690s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2108000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002108s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2117000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002117s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1711000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001711s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1766000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001766s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2095000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002095s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4540000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004540s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2104000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002104s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2613000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002613s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2094000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002094s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1750000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001750s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1722000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001722s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1395000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001395s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2108000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002108s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3164000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003164s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1715000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001715s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1761000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001761s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 724000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000724s"
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
          "id": "396302d6585f057e6446973cf5de252112a7ef5b",
          "message": "Use the WfIRContext API for PatternRewriter (#424)\n\nChange `PatternRewriter` and `Pass` to use an `WfIRContext` instead of\nan `IRContext` with a proof of well-formedness.\n\nI benchmarked it, and there seems to be no changes.",
          "timestamp": "2026-04-17T13:27:44Z",
          "tree_id": "8bee09b4b863f1dc4376afee88b845764ee2ce7c",
          "url": "https://github.com/opencompl/veir/commit/396302d6585f057e6446973cf5de252112a7ef5b"
        },
        "date": 1776433132709,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2118000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002118s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3185000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003185s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2152000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002152s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2648000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002648s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2238000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002238s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2141000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002141s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1762000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001762s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1779000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001779s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2144000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002144s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4688000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004688s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2114000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002114s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2587000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002587s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2172000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002172s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1731000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001731s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1748000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001748s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1393000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001393s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2129000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002129s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3150000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003150s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1743000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001743s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1779000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001779s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 724000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000724s"
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
          "id": "76cc557a57ff69930c164821e0a9ea8aff4c6785",
          "message": "Use a struct for `WfIRContext`. (#425)\n\nAlso, name the field `raw`, as we are going to rename `IRContext` to\n`RawIRContext` in the very near future.",
          "timestamp": "2026-04-17T17:38:29Z",
          "tree_id": "adbd8e9e448f5d119a8f10cd526b7961658a57c5",
          "url": "https://github.com/opencompl/veir/commit/76cc557a57ff69930c164821e0a9ea8aff4c6785"
        },
        "date": 1776448164254,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2304000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002304s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3664000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003664s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2245000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002245s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3069000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003069s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2188000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002188s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2332000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002332s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1909000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001909s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1912000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001912s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2195000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002195s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5155000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005155s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2150000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002150s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2974000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002974s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2226000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002226s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1911000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001911s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1840000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001840s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1525000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001525s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2215000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002215s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3607000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003607s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1859000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001859s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1824000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001824s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 743000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000743s"
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
          "id": "87095913c5c9f51b37db7b305427a6538eae7ab7",
          "message": "Ensure operand arrays matching can be reasoned about. (#426)",
          "timestamp": "2026-04-17T19:45:46Z",
          "tree_id": "0332849a730ecd29db18c5fcc9dee5b06cc97828",
          "url": "https://github.com/opencompl/veir/commit/87095913c5c9f51b37db7b305427a6538eae7ab7"
        },
        "date": 1776455306770,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1875000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001875s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3401000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003401s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1861000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001861s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2895000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002895s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1855000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001855s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2138000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002138s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1594000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001594s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1753000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001753s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1878000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001878s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4799000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004799s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1859000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001859s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2679000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002679s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1868000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001868s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1732000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001732s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1575000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001575s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1362000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001362s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1853000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001853s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3230000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003230s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1587000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001587s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1592000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001592s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 766000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000766s"
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
          "id": "a4a6f17f4b87aa871ddca12e5f541b3dd88ad3cb",
          "message": "Ensure docs lean-toolchain version matches the version used for non-doc builds (#429)\n\nDocs builds should use the same `lean-toolchain` as the non-doc builds.\nWe implement this by making the doc lean-toolchain a symlink to the main\nlean-toolchain. The current version mismatch has caused some\ninconsistencies, including a failure when axioms in modules were not yet\nsupported in the doc builds. We also remove in this PR the workaround we\ncommitted in #422, which was due to not identifying this version\nmismatch.\n\nWe also change the nightly update script to update the `docbuild`\ndirectory.",
          "timestamp": "2026-04-18T16:16:16Z",
          "tree_id": "b76c5c94a931ad821d4f9824d7ad5d969a0f8637",
          "url": "https://github.com/opencompl/veir/commit/a4a6f17f4b87aa871ddca12e5f541b3dd88ad3cb"
        },
        "date": 1776529278532,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2217000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002217s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3773000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003773s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2286000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002286s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3123000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003123s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2201000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002201s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2468000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002468s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1909000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001909s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1992000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001992s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2313000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002313s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5368000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005368s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2344000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002344s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3068000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003068s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2354000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002354s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1979000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001979s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1906000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001906s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1545000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001545s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2245000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002245s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3699000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003699s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1829000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001829s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1836000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001836s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 786000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000786s"
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
          "id": "ac5b91ac3fb002622f2883167b8cf997709a3dd1",
          "message": "Modularize more Lean files (#427)\n\n`Rewriter/WellFormed/Basic.lean` is now renamed to\n`Rewriter/WellFormed.lean`, and uses public imports since it is used to\nimport the entire folder.",
          "timestamp": "2026-04-18T18:21:14Z",
          "tree_id": "73be81e97fcc4df74dfcdefe76c376bbbd2a96bc",
          "url": "https://github.com/opencompl/veir/commit/ac5b91ac3fb002622f2883167b8cf997709a3dd1"
        },
        "date": 1776545118828,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2256000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002256s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3752000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003752s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2237000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002237s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3218000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003218s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2223000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002223s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2402000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002402s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1797000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001797s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2010000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002010s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2269000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002269s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5413000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005413s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2214000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002214s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3112000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003112s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2331000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002331s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1977000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001977s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1744000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001744s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1587000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001587s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2226000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002226s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3727000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003727s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1876000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001876s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1886000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001886s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 788000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000788s"
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
          "id": "458c55c7a1d1c87e098bb2acddfd730f102c5bd8",
          "message": "nightly-2026-04-19 lean nightly update (#436)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-04-19T15:07:50Z",
          "tree_id": "2238a0bb5961ac760181da43b4dd711995289950",
          "url": "https://github.com/opencompl/veir/commit/458c55c7a1d1c87e098bb2acddfd730f102c5bd8"
        },
        "date": 1776611413901,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2375000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002375s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3744000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003744s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2446000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002446s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3161000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003161s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2282000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002282s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2444000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002444s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1891000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001891s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2011000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002011s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2323000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002323s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5266000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005266s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2377000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002377s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3023000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003023s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2331000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002331s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1978000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001978s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1947000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001947s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1569000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001569s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2361000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002361s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3768000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003768s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1920000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001920s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1933000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001933s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 809000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000809s"
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
          "id": "ca80355e208c14bb8574c08d156c4cad0b33d393",
          "message": "Use ExtHashMap for the interpreter state (#430)\n\nThis will allow us to more easily reason about the interpreter state, as\nwe can then use equality between states instead of defining a property\nfor it.\n\n---------\n\nCo-authored-by: Léo Stefanesco <leo.lveb@gmail.com>",
          "timestamp": "2026-04-19T17:08:38Z",
          "tree_id": "2931ba24bc810d8c3a9bc0be824b5a4b4e4dd5d5",
          "url": "https://github.com/opencompl/veir/commit/ca80355e208c14bb8574c08d156c4cad0b33d393"
        },
        "date": 1776618683981,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2212000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002212s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3712000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003712s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2300000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002300s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3115000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003115s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2346000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002346s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2450000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002450s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1892000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001892s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1962000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001962s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2236000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002236s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5291000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005291s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2258000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002258s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3031000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003031s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2349000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002349s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1965000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001965s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1896000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001896s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1542000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001542s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2353000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002353s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3670000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003670s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1874000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001874s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1949000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001949s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 793000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000793s"
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
          "id": "6ffbc28e97fcc0fc1c467a8f1612708a28d78166",
          "message": "Add InsertPoint.after (#431)\n\nThis is a constructor to build an `InsertPoint` that points after an\noperation. It requires to pass the operation parent block, as we can\nonly get the InsertPoint after an operation if it has a parent.\n\nAlso, add two `simp` annotations that were missing.",
          "timestamp": "2026-04-19T17:20:06Z",
          "tree_id": "a33697e56cb25d42d0aeaf322d47e4d6bbb1ab7f",
          "url": "https://github.com/opencompl/veir/commit/6ffbc28e97fcc0fc1c467a8f1612708a28d78166"
        },
        "date": 1776619700600,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1878000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001878s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3493000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003493s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1881000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001881s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2926000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002926s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1863000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001863s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2196000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002196s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1609000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001609s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1853000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001853s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1871000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001871s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4990000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004990s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1860000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001860s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2755000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002755s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1888000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001888s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1780000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001780s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1576000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001576s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1408000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001408s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1843000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001843s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3339000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003339s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1604000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001604s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1588000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001588s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 802000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000802s"
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
          "distinct": false,
          "id": "3628612e31cc3d6072c3fc7bf2a8e9a7108af138",
          "message": "Add some lemmas about the interpreter (#432)\n\nThese are going to be useful later on for reasonning about the\ninterpreter.",
          "timestamp": "2026-04-19T19:36:24Z",
          "tree_id": "5c75e0b316236defccfa6225b0c2fd2661b12224",
          "url": "https://github.com/opencompl/veir/commit/3628612e31cc3d6072c3fc7bf2a8e9a7108af138"
        },
        "date": 1776627525540,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2324000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002324s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3718000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003718s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2378000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002378s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3052000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003052s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2359000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002359s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2400000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002400s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1997000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001997s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1929000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001929s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2296000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002296s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5247000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005247s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2384000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002384s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2999000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002999s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2384000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002384s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2039000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002039s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1967000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001967s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1612000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001612s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2365000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002365s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3833000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003833s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1891000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001891s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1971000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001971s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 775000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000775s"
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
          "id": "475c18e7c05f59dde8f9035e50f2238a33d6d2e7",
          "message": "continue CI on documentation errors (#440)\n\nDocumentation errors cause unnecessary noise on the CI and it seems the\nLean documentation story is currently a bit unstable. Hence, let's hide\nthese errors for now. We can re-evaluate this in the future when the\ndocumentation story got a bit stronger.",
          "timestamp": "2026-04-20T05:45:11Z",
          "tree_id": "f52e223241f847fe552abd0099fe4155aac46ee0",
          "url": "https://github.com/opencompl/veir/commit/475c18e7c05f59dde8f9035e50f2238a33d6d2e7"
        },
        "date": 1776664052891,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1881000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001881s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3491000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003491s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1866000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001866s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2936000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002936s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1877000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001877s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2193000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002193s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1613000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001613s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1800000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001800s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1881000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001881s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4968000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004968s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1876000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001876s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2782000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002782s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1894000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001894s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1773000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001773s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1574000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001574s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1396000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001396s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1889000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001889s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3334000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003334s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1603000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001603s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1587000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001587s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 779000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000779s"
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
          "id": "24561ec8d02eed770e180d34658593f7ffae40a5",
          "message": "continue CI on documentation errors II (#441)\n\nFor this to work we also need to ignore unavailable artifacts.",
          "timestamp": "2026-04-20T06:51:49Z",
          "tree_id": "a7c93407d210fd2f1dd35a23227bc64b58f4b033",
          "url": "https://github.com/opencompl/veir/commit/24561ec8d02eed770e180d34658593f7ffae40a5"
        },
        "date": 1776668048825,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2330000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002330s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3697000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003697s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2283000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002283s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3064000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003064s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2321000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002321s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2442000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002442s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1853000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001853s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1915000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001915s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2331000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002331s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5348000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005348s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2208000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002208s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2988000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002988s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2266000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002266s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2001000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002001s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1824000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001824s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1535000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001535s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2282000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002282s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 4079000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004079s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1742000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001742s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1860000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001860s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 783000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000783s"
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
          "id": "5d5ba8935d0d3b07798f83f3b8400fd3e32a71c3",
          "message": "continue CI on documentation errors III (#442)\n\nUse `; true` to properly surpress the error code",
          "timestamp": "2026-04-20T07:06:41Z",
          "tree_id": "6a83aa687d7eace04c02f1cd3079c34ba5f76d27",
          "url": "https://github.com/opencompl/veir/commit/5d5ba8935d0d3b07798f83f3b8400fd3e32a71c3"
        },
        "date": 1776668941906,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2336000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002336s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3698000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003698s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2344000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002344s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3090000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003090s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2342000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002342s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2400000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002400s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1977000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001977s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1986000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001986s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2396000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002396s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5225000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005225s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2271000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002271s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2977000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002977s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2349000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002349s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1990000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001990s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1984000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001984s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1535000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001535s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2308000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002308s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3616000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003616s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1899000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001899s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2027000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002027s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 846000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000846s"
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
          "id": "faeb1ffb4cec15c6af8554dfbea754a2c545d7ad",
          "message": "continue CI on documentation errors IV (#443)",
          "timestamp": "2026-04-20T07:20:00Z",
          "tree_id": "75e6a0c4b1159c87046303a711510f38697b94c0",
          "url": "https://github.com/opencompl/veir/commit/faeb1ffb4cec15c6af8554dfbea754a2c545d7ad"
        },
        "date": 1776669743524,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1988000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001988s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3544000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003544s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1877000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001877s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2907000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002907s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1976000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001976s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2299000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002299s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1615000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001615s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1827000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001827s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1933000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001933s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4945000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004945s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1879000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001879s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2812000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002812s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1867000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001867s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1808000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001808s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1604000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001604s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1427000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001427s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1908000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001908s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3337000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003337s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1589000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001589s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1585000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001585s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 780000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000780s"
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
          "id": "7b4bf85c052f9673f398e52757cb298665a94b91",
          "message": "Improve low-level lemmas on `OperationPtr.getOperand` (#437)\n\nAlso, fix `OperationPtr.getOperand` definition to use a `!` definition.",
          "timestamp": "2026-04-20T12:11:10Z",
          "tree_id": "4deb378023bce76fbd807602cf72dbbde315afc4",
          "url": "https://github.com/opencompl/veir/commit/7b4bf85c052f9673f398e52757cb298665a94b91"
        },
        "date": 1776687909926,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2270000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002270s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3724000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003724s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2347000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002347s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3078000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003078s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2556000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002556s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2394000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002394s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2016000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002016s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1969000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001969s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2566000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002566s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5357000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005357s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2435000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002435s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2966000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002966s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2465000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002465s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1971000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001971s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1944000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001944s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1577000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001577s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2424000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002424s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3780000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003780s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2093000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002093s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2197000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002197s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 793000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000793s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "74881848+nchappe@users.noreply.github.com",
            "name": "nchappe",
            "username": "nchappe"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "6b58b09e7d766b4d794d6b8ceb5847c1615df0de",
          "message": "Interpret `cf.br` (#418)\n\nBlocks to interpret are iterated over using a `partial_fixpoint`,\nuntil a `func.return` terminator is eventually reached (if any).",
          "timestamp": "2026-04-20T12:57:28Z",
          "tree_id": "d6f8e41a076c8e18665d1f7be9b7597d28f3fe74",
          "url": "https://github.com/opencompl/veir/commit/6b58b09e7d766b4d794d6b8ceb5847c1615df0de"
        },
        "date": 1776690019231,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2160000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002160s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3205000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003205s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2157000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002157s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2646000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002646s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2106000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002106s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2087000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002087s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1734000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001734s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1742000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001742s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2098000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002098s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4486000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004486s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2127000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002127s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2585000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002585s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2097000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002097s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1744000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001744s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1720000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001720s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1399000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001399s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2105000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002105s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3062000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003062s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1712000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001712s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1711000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001711s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 719000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000719s"
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
          "id": "16bc9ae5193261393698dacc7bcf954bb5657218",
          "message": "Implement `OperationPtr.getOpResults` and `OperationPtr.getResults` (#438)\n\nAs well as their associated lemmas. This is mostly a copy-paste of\n`OperationPtr.getOperands`.\n\nThere is two versions of this since we might want to return an array of\n`ValuePtr` or `OpResultPtr`.",
          "timestamp": "2026-04-20T13:19:05Z",
          "tree_id": "386d45ed07c7b8dc38b8c984825401927a1bb075",
          "url": "https://github.com/opencompl/veir/commit/16bc9ae5193261393698dacc7bcf954bb5657218"
        },
        "date": 1776691960056,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2484000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002484s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3714000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003714s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2391000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002391s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3117000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003117s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2406000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002406s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2421000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002421s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1992000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001992s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1933000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001933s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2357000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002357s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5222000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005222s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2256000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002256s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2972000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002972s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2398000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002398s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1936000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001936s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1950000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001950s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1525000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001525s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2383000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002383s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3663000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003663s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2028000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002028s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1946000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001946s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 769000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000769s"
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
          "id": "82f8e86ed63a6993b9a90d33c25189d05544d745",
          "message": "Improve lemma on `getResults` and `getOperands` (#439)\n\nUse an `iff` instead of an implication.",
          "timestamp": "2026-04-20T14:09:40Z",
          "tree_id": "54f8566f2cbdf97e1ba822e23b0491e4bfea26e4",
          "url": "https://github.com/opencompl/veir/commit/82f8e86ed63a6993b9a90d33c25189d05544d745"
        },
        "date": 1776695009198,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2236000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002236s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3811000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003811s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2234000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002234s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3147000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003147s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2283000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002283s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2412000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002412s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1920000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001920s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1953000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001953s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2255000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002255s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5305000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005305s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2347000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002347s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3056000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003056s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2263000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002263s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1968000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001968s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1821000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001821s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1551000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001551s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2192000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002192s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3678000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003678s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1849000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001849s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1862000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001862s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 771000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000771s"
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
          "id": "47563992e5cc7ab7fc2cb461d5a65644198a867e",
          "message": "Fix compilation of `Interpreter/Lemmas.lean` (#447)\n\nThe file was not imported from anywhere.",
          "timestamp": "2026-04-20T16:41:39Z",
          "tree_id": "b085c88b11b6223c269041fc7cf7bd981f2c5b51",
          "url": "https://github.com/opencompl/veir/commit/47563992e5cc7ab7fc2cb461d5a65644198a867e"
        },
        "date": 1776703442015,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2224000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002224s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3720000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003720s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2162000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002162s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3112000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003112s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2232000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002232s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2412000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002412s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1875000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001875s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1930000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001930s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2335000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002335s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5309000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005309s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2393000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002393s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3046000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003046s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2235000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002235s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1957000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001957s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1893000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001893s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1529000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001529s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2314000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002314s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3616000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003616s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1973000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001973s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1906000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001906s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 743000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000743s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "74881848+nchappe@users.noreply.github.com",
            "name": "nchappe",
            "username": "nchappe"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "32c42f8cdf231a68a5da10d64adb96a1b42a96e6",
          "message": "Parse and verify `cf.cond_br` (#446)\n\nThis depends on #445.\nBecause `cf.cond_br` takes variadic operands there is some magic with\nthe `operandSegmentSizes` property, I handle that in an ad-hoc way for\nnow.",
          "timestamp": "2026-04-20T18:17:53Z",
          "tree_id": "22b29ebd2efe0f2845bc7331dc7b2f3d2c40d658",
          "url": "https://github.com/opencompl/veir/commit/32c42f8cdf231a68a5da10d64adb96a1b42a96e6"
        },
        "date": 1776709294114,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2074000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002074s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3148000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003148s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2085000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002085s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2596000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002596s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2058000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002058s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2069000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002069s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1698000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001698s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1734000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001734s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2078000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002078s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4412000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004412s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2078000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002078s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2591000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002591s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2065000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002065s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1707000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001707s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1674000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001674s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1369000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001369s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2071000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002071s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3064000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003064s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1676000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001676s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1687000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001687s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 718000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000718s"
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
          "id": "2d47c650daf6c6624a0d8d0761d20dda7edff29d",
          "message": "Implement `ValuePtr.getDefiningOp` (#449)\n\nThis function is quite useful to check if a value is an operation\nresult, and get the operation defining it at the same time.",
          "timestamp": "2026-04-20T20:12:06Z",
          "tree_id": "607b5b13d78a0d9a1db99ce6f82200a98b71a8db",
          "url": "https://github.com/opencompl/veir/commit/2d47c650daf6c6624a0d8d0761d20dda7edff29d"
        },
        "date": 1776716798884,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2263000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002263s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3711000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003711s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2264000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002264s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3113000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003113s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2174000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002174s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2376000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002376s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1866000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001866s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1931000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001931s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2244000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002244s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5163000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005163s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2294000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002294s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3008000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003008s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2215000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002215s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1932000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001932s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1913000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001913s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1529000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001529s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2202000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002202s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3640000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003640s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1896000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001896s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1847000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001847s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 741000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000741s"
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
          "distinct": false,
          "id": "19225af9d7fe9cd852f2e7ad1f596dafc514a864",
          "message": "riscv: combine and proof automation (#450)\n\nWe add a `right_identity_op_add` combine that folds `riscv.add lhs 0 ->\nlhs`, including an automation simp-set to prove the semantics\nequivalence. The name is the same used in\n[LLVM](https://github.com/llvm/llvm-project/blob/ab4283959fd10fa347e0a60507b7101ad273fc57/llvm/include/llvm/Target/GlobalISel/Combine.td#L554).\nIn LLVM, this combine lives at the generic machine IR level (GMIR), and\nis therefore not riscv-specific. However, at the moment, we introduce a\nnew namespace `Veir.RISCV` where these combines live, together with the\nproofs and the matching methods. In the future we can replace this with,\ne.g., a GMIR namespace that can match different backends.\n\nConcerning the proof automation, we introduce a new `reg_toBitVec` simp\nset, copying the design from the way Lean treats `UInt*` types. This set\nunfolds the semantics of `Reg` operations to `BitVec` operations.",
          "timestamp": "2026-04-22T08:49:59Z",
          "tree_id": "160276c872d1cbad13eed9f17259f356525d4bea",
          "url": "https://github.com/opencompl/veir/commit/19225af9d7fe9cd852f2e7ad1f596dafc514a864"
        },
        "date": 1776847978522,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1874000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001874s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3402000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003402s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1886000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001886s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2912000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002912s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1888000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001888s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2196000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002196s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1567000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001567s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1792000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001792s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1861000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001861s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4797000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004797s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1869000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001869s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2773000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002773s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1851000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001851s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1732000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001732s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1556000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001556s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1409000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001409s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1971000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001971s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3238000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003238s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1563000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001563s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1604000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001604s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 761000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000761s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "74881848+nchappe@users.noreply.github.com",
            "name": "nchappe",
            "username": "nchappe"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9cb8d98c8ff478612e4813bf506fb0d5d3559b67",
          "message": "Interpret `cf.cond_br` (#452)\n\nThis uses the `operandSegmentSizes` property to extract the relevant\noperands depending on the value of the condition.",
          "timestamp": "2026-04-22T08:50:48Z",
          "tree_id": "0f47e02e3c15c788b5eb7774e2e8965e9491e30c",
          "url": "https://github.com/opencompl/veir/commit/9cb8d98c8ff478612e4813bf506fb0d5d3559b67"
        },
        "date": 1776847994761,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2217000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002217s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3722000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003722s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2229000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002229s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3135000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003135s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2227000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002227s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2403000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002403s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1924000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001924s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1957000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001957s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2228000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002228s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5207000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005207s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2204000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002204s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3011000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003011s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2282000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002282s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1939000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001939s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1884000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001884s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1510000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001510s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2202000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002202s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3584000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003584s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1913000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001913s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1833000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001833s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 754000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000754s"
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
          "id": "fdf7e26f2e9850084f09d2ab4612414fef1d5fab",
          "message": "Remove unpacking of array (#453)\n\nUnpacking arrays doesn't produce the right lemmas to reason about it, so\nwe should convert it to a list first.",
          "timestamp": "2026-04-22T12:15:18Z",
          "tree_id": "36b9547ce8cc53352833aa1604f53ec3cb8f9b8d",
          "url": "https://github.com/opencompl/veir/commit/fdf7e26f2e9850084f09d2ab4612414fef1d5fab"
        },
        "date": 1776860283735,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2236000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002236s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3739000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003739s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2286000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002286s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3161000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003161s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2269000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002269s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2398000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002398s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1860000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001860s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1996000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001996s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2181000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002181s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5250000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005250s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2164000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002164s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3022000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003022s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2259000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002259s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1939000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001939s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1823000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001823s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1513000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001513s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2279000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002279s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3608000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003608s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1939000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001939s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1895000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001895s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 768000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000768s"
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
          "id": "c99f543d9275d685c49ff6202537d98d1755484e",
          "message": "nightly-2026-04-22 lean nightly update (#454)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-04-22T15:17:38Z",
          "tree_id": "d30e3a2a904359bcf6ce073d80d51d89c1e3c575",
          "url": "https://github.com/opencompl/veir/commit/c99f543d9275d685c49ff6202537d98d1755484e"
        },
        "date": 1776871207029,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2282000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002282s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3789000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003789s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2288000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002288s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3186000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003186s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2336000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002336s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2436000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002436s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1922000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001922s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1936000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001936s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2313000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002313s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5423000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005423s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2385000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002385s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3066000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003066s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2208000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002208s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1967000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001967s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1886000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001886s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1573000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001573s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2271000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002271s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3733000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003733s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1869000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001869s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1932000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001932s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 804000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000804s"
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
          "distinct": false,
          "id": "83098a833fac3b2e37a9a15470f2baece72499eb",
          "message": "Decidable instances for (Block)InsertPoint.InBounds (#434)\n\n~~Required by #222.~~\nRequired by #435.",
          "timestamp": "2026-04-23T15:36:54Z",
          "tree_id": "0379f6b2f23ef3e1a5bde3d159b5d459d1fcb0bd",
          "url": "https://github.com/opencompl/veir/commit/83098a833fac3b2e37a9a15470f2baece72499eb"
        },
        "date": 1776959139254,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2380000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002380s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3818000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003818s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2354000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002354s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3191000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003191s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2240000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002240s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2434000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002434s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1915000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001915s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1969000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001969s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2313000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002313s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5339000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005339s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2290000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002290s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3064000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003064s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2214000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002214s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1963000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001963s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1825000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001825s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1523000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001523s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2243000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002243s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3690000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003690s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1931000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001931s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1841000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001841s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 761000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000761s"
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
          "id": "1f0a1367140ca50469f548bb9f4aa30691fdf4f8",
          "message": "nightly-2026-04-24 lean nightly update (#462)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-04-24T16:26:56Z",
          "tree_id": "1c0b51d302d2c55b74beca545b411d127fde37e2",
          "url": "https://github.com/opencompl/veir/commit/1f0a1367140ca50469f548bb9f4aa30691fdf4f8"
        },
        "date": 1777048160132,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2246000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002246s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3675000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003675s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2307000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002307s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3094000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003094s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2223000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002223s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2400000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002400s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1809000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001809s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1924000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001924s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2317000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002317s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5172000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005172s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2250000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002250s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2963000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002963s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2267000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002267s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1928000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001928s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1871000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001871s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1530000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001530s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2281000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002281s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3607000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003607s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1891000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001891s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1841000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001841s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 742000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000742s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "74881848+nchappe@users.noreply.github.com",
            "name": "nchappe",
            "username": "nchappe"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "e890e75e69d943e49d1cbd701550357fbf8a39ab",
          "message": "Add `llvm.br` and `llvm.cond_br` (#461)\n\nThey are the same as in the `cf` dialect.",
          "timestamp": "2026-04-24T19:32:14Z",
          "tree_id": "14dce19f5d710b77c2a5cd949774d10a20e2ea3f",
          "url": "https://github.com/opencompl/veir/commit/e890e75e69d943e49d1cbd701550357fbf8a39ab"
        },
        "date": 1777059365353,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2332000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002332s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3730000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003730s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2394000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002394s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3151000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003151s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2369000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002369s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2461000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002461s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2040000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002040s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1912000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001912s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2358000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002358s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5265000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005265s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2496000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002496s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3035000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003035s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2303000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002303s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1956000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001956s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1963000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001963s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1567000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001567s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2483000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002483s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3818000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003818s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2145000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002145s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2067000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002067s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 745000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000745s"
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
          "id": "911a5f8bcd0b16554001064a0c94934c9a5d921c",
          "message": "Add lemmas about the interpreter and dominance (#451)\n\nSince we do not have a dominance theory yet, we add a list of axioms for\nnow.\n\nCo-authored-by: Tobias Grosser <tobias@grosser.es>",
          "timestamp": "2026-04-25T03:30:57Z",
          "tree_id": "1ec513ea97e9908fd37c05176bfc3e2c0e5e1629",
          "url": "https://github.com/opencompl/veir/commit/911a5f8bcd0b16554001064a0c94934c9a5d921c"
        },
        "date": 1777088015541,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1850000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001850s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3374000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003374s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1904000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001904s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2916000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002916s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1873000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001873s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2188000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002188s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1559000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001559s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1738000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001738s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1861000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001861s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4805000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004805s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1841000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001841s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2693000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002693s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1859000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001859s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1731000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001731s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1580000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001580s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1386000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001386s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1860000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001860s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3273000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003273s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1570000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001570s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1572000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001572s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 767000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000767s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "siddu.druid@gmail.com",
            "name": "Siddharth",
            "username": "bollu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "03448eac4e941193dc702f7a3caaaf732e226223",
          "message": "feat: new packed float datatype (#463)\n\nThis PR adds a new `PackedFloat e s` datatype that represents an IEEE\nformatted floating point number with `e` bits of exponent and `s` bits\nof significand.\n\n---------\n\nCo-authored-by: Luisa Cicolini <48860705+luisacicolini@users.noreply.github.com>\nCo-authored-by: Tobias Grosser <github@grosser.es>",
          "timestamp": "2026-04-27T10:09:18Z",
          "tree_id": "27b97d52815921117a8bd94a01e88949bc439463",
          "url": "https://github.com/opencompl/veir/commit/03448eac4e941193dc702f7a3caaaf732e226223"
        },
        "date": 1777284712045,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 3404000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.003404s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 4036000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004036s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 3359000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.003359s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3467000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003467s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 3472000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.003472s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 3102000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003102s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2951000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002951s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2707000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002707s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 3560000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.003560s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5730000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005730s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 3367000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.003367s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3304000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003304s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 3416000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.003416s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2315000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002315s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2818000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002818s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 2061000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002061s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 3554000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.003554s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3966000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003966s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2904000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002904s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2537000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002537s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 996000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000996s"
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
          "id": "19f36398b186b88d8f5b19aee7a3aa4542f45627",
          "message": "nightly-2026-04-27 lean nightly update (#464)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-04-27T15:49:28Z",
          "tree_id": "55a7bf68d38d0c2657c3c24375f7a033277cb723",
          "url": "https://github.com/opencompl/veir/commit/19f36398b186b88d8f5b19aee7a3aa4542f45627"
        },
        "date": 1777305113939,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2296000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002296s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3728000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003728s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2263000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002263s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3086000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003086s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2241000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002241s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2525000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002525s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1818000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001818s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2001000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002001s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2258000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002258s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5278000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005278s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2293000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002293s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2968000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002968s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2395000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002395s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1956000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001956s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1829000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001829s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1523000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001523s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2155000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002155s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3608000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003608s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1945000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001945s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2017000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002017s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 803000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000803s"
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
          "id": "61d4ca7bfac4805bfcef7e4d1e5923b692b60511",
          "message": "Definition of the equation lemma (#433)\n\nDefines the equation lemma, as well as an invariant on\n`InterpreterState` to state that every dominating operation satisfies\nthe equation lemma.",
          "timestamp": "2026-04-27T16:38:13Z",
          "tree_id": "c0d3f98af12dc92138c8fc78293c677f1d360ab5",
          "url": "https://github.com/opencompl/veir/commit/61d4ca7bfac4805bfcef7e4d1e5923b692b60511"
        },
        "date": 1777308053148,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1863000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001863s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3451000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003451s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1876000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001876s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2865000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002865s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1956000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001956s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2145000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002145s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1584000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001584s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1710000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001710s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1853000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001853s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4806000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004806s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1892000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001892s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2712000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002712s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1887000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001887s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1755000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001755s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1599000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001599s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1399000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001399s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1850000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001850s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3230000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003230s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1594000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001594s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1590000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001590s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 763000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000763s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "74881848+nchappe@users.noreply.github.com",
            "name": "nchappe",
            "username": "nchappe"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "422271dca70f89c595425158e716ab846508b10a",
          "message": "Factor out handling of unit attrs (#465)\n\nThis will make it easier to add LLVM memory operations, as they have\nquite a few unit attributes.",
          "timestamp": "2026-04-27T17:18:04Z",
          "tree_id": "a68554b3fe88758e5dd58c6de69861e63c3bde01",
          "url": "https://github.com/opencompl/veir/commit/422271dca70f89c595425158e716ab846508b10a"
        },
        "date": 1777311137274,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1878000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001878s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3422000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003422s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1867000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001867s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2844000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002844s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1856000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001856s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2173000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002173s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1561000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001561s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1719000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001719s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1847000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001847s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4793000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004793s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1915000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001915s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2724000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002724s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1868000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001868s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1765000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001765s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1596000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001596s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1394000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001394s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1890000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001890s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3289000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003289s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1604000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001604s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1567000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001567s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 769000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000769s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "georgerennie@gmail.com",
            "name": "George Rennie",
            "username": "georgerennie"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "96dfbf8a933b8bc9ac5461dbb5fd8cfc48a9c5a4",
          "message": "comb: Add CIRCT's comb dialect (#466)\n\nThis adds the basic definitions of operations from CIRCT's comb dialect,\nproviding only the basic syntactic definitions/verifier, not semantic\ndefinitions. The `comb.truth_table` operation is currently missing as it\nrequires `DenseBoolArrayAttr` which is not implemented in VEIR yet.\n\nThis also adds a basic filecheck test that just parses/prints each of\nthe added ops. The variadic ops are repeated for varying numbers of\narguments and `comb.icmp` instantiated for each valid `predicate` value.",
          "timestamp": "2026-04-28T13:06:43Z",
          "tree_id": "f4ae6d46a00caac228eea8d501b3e4dd780c8bd0",
          "url": "https://github.com/opencompl/veir/commit/96dfbf8a933b8bc9ac5461dbb5fd8cfc48a9c5a4"
        },
        "date": 1777381844517,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2448000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002448s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3803000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003803s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2697000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002697s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3342000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003342s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2668000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002668s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2694000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002694s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2258000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002258s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2045000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002045s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2637000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002637s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5595000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005595s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2655000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002655s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3129000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003129s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2541000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002541s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2057000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002057s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2328000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002328s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1650000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001650s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2496000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002496s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3843000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003843s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2077000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002077s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2213000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002213s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 784000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000784s"
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
          "distinct": false,
          "id": "a8a7759f769a773ec9b243636281d8681ef2e111",
          "message": "Add GetSet lemmas for `Rewriter.createOp` (#467)\n\nAlso, add a few lemmas that were missing from the file that were needed\nto write these get-set lemmas.",
          "timestamp": "2026-04-28T16:05:42Z",
          "tree_id": "be58900339db6020712fd210c6e36638219911ba",
          "url": "https://github.com/opencompl/veir/commit/a8a7759f769a773ec9b243636281d8681ef2e111"
        },
        "date": 1777393382070,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2345000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002345s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3742000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003742s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2319000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002319s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3155000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003155s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2360000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002360s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2467000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002467s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1952000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001952s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1990000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001990s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2273000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002273s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5332000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005332s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2295000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002295s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3051000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003051s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2254000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002254s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1986000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001986s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1957000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001957s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1573000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001573s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2231000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002231s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3731000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003731s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2090000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002090s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1936000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001936s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 789000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000789s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "siddu.druid@gmail.com",
            "name": "Siddharth",
            "username": "bollu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "94d570aa329af40e85a89b41996f3baa863afb2d",
          "message": "feat: PackedFloat.ofFloat/toFloat to coerce Lean's floats into FP model floats (#471)\n\nThis PR adds suppport for coercing Lean's `Float` (double precision)\nfloating point type into a `FP.PackedFloat` (our model of floating\npoint)\nand back. \n\nThis then allows us to develop a uniform API to perform floating point\noperations on `FP.PackedFloat` values by converting to lean `Float`,\nperforming the operation, and then converting back to `FP.PackedFloat`\n(with appropriate rounding), as long as the simulated float fits in the\nlean `Float`.",
          "timestamp": "2026-04-29T07:18:38Z",
          "tree_id": "b5d5ff5eac4157af20347ae3e27ec245244b896e",
          "url": "https://github.com/opencompl/veir/commit/94d570aa329af40e85a89b41996f3baa863afb2d"
        },
        "date": 1777447273763,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1828000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001828s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3451000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003451s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1832000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001832s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2849000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002849s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1824000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001824s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2174000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002174s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1574000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001574s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1760000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001760s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2028000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002028s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4853000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004853s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1822000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001822s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2755000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002755s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1854000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001854s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1731000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001731s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1549000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001549s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1388000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001388s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1840000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001840s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3284000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003284s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1548000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001548s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1517000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001517s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 755000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000755s"
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
          "distinct": false,
          "id": "677d001acf26fb623a23290a71b6901a4143614f",
          "message": "Add support for `getSuccessor` in the rewriter get-set lemmas (#468)\n\nWhile `getSuccessor op ctx index` is just a wrapper around\n`((BlockOperandPtr.mk op index).get! ctx).value`, I think it is still\nworth to provide get-set lemmas for it, especially since we will need\n`getSuccessors` lemmas (that are quite needed from what I've seen).",
          "timestamp": "2026-04-29T16:39:55Z",
          "tree_id": "366485bcca0a2218ed281bbe8a1fc671b9c8af87",
          "url": "https://github.com/opencompl/veir/commit/677d001acf26fb623a23290a71b6901a4143614f"
        },
        "date": 1777481695279,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1451000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001451s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 2703000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002703s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1454000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001454s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2233000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002233s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1435000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001435s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 1659000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001659s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1225000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001225s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1365000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001365s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1444000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001444s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 3763000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003763s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1423000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001423s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2085000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002085s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1432000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001432s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1332000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001332s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1206000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001206s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1070000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001070s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1447000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001447s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 2510000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002510s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1219000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001219s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1203000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001203s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 586000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000586s"
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
          "id": "bb3d3ce483f2751e9f256018d584ac2871c91d4e",
          "message": "nightly-2026-04-29 lean nightly update (#476)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-04-29T16:49:03Z",
          "tree_id": "758db30cf87a4f586dfab9f59c87b5a497bc1de7",
          "url": "https://github.com/opencompl/veir/commit/bb3d3ce483f2751e9f256018d584ac2871c91d4e"
        },
        "date": 1777482486793,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1984000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001984s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3490000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003490s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1981000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001981s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2933000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002933s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1895000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001895s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2177000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002177s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1562000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001562s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1755000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001755s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1890000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001890s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4846000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004846s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1899000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001899s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2717000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002717s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1889000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001889s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1737000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001737s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1576000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001576s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1388000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001388s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2062000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002062s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3390000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003390s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1547000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001547s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1588000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001588s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 776000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000776s"
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
          "id": "e6b78098c179e7d55db59e7252b7eb6a0b0c964b",
          "message": "Implement `getSuccessors` (#469)\n\nAlso, add the get-set lemmas for `getSuccessors` in the rewriter.",
          "timestamp": "2026-04-29T16:52:50Z",
          "tree_id": "3b5c23d3a24227c3e911af774e84558765b8f8e3",
          "url": "https://github.com/opencompl/veir/commit/e6b78098c179e7d55db59e7252b7eb6a0b0c964b"
        },
        "date": 1777482673554,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2528000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002528s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3898000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003898s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2462000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002462s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3233000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003233s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2526000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002526s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2478000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002478s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2247000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002247s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2009000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002009s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2468000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002468s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5441000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005441s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2430000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002430s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3116000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003116s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2573000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002573s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1995000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001995s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2084000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002084s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1601000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001601s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2518000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002518s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3744000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003744s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2053000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002053s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2061000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002061s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 788000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000788s"
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
          "distinct": false,
          "id": "f53ec92316f5f6024cc3131e30ca2b767878dbfd",
          "message": "Use `OperationPtr.getSuccessors` in the interpreter (#470)",
          "timestamp": "2026-04-29T17:15:37Z",
          "tree_id": "f6c9ea14e58be16c92e0175452e738289b6f12fb",
          "url": "https://github.com/opencompl/veir/commit/f53ec92316f5f6024cc3131e30ca2b767878dbfd"
        },
        "date": 1777483117461,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2262000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002262s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3816000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003816s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2292000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002292s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3186000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003186s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2264000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002264s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2449000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002449s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1925000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001925s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2000000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002000s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2317000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002317s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5362000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005362s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2355000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002355s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3064000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003064s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2436000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002436s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2024000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002024s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1993000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001993s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1587000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001587s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2360000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002360s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3705000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003705s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2028000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002028s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2075000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002075s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 791000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000791s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "74881848+nchappe@users.noreply.github.com",
            "name": "nchappe",
            "username": "nchappe"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "275a7beb43517e70d92c24b825522b7ff190262c",
          "message": "Parse and verify basic LLVM memory operations (#475)\n\nDepends on #474.\n\nI left out the few properties (notably the atomic memory orderings) that\nrequire enum support.",
          "timestamp": "2026-04-29T20:52:13Z",
          "tree_id": "37830352ba258d2a7d9ded1c649989e64cb41a36",
          "url": "https://github.com/opencompl/veir/commit/275a7beb43517e70d92c24b825522b7ff190262c"
        },
        "date": 1777496994873,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2208000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002208s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3851000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003851s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2260000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002260s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3155000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003155s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2302000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002302s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2443000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002443s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1869000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001869s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2007000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002007s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2338000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002338s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5358000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005358s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2345000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002345s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3065000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003065s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2318000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002318s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1998000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001998s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1845000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001845s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1584000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001584s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2309000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002309s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3742000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003742s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1945000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001945s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1882000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001882s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 786000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000786s"
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
          "id": "7fbfdd9d4fe8a6c68341f1a4959993bfa3aa8d8a",
          "message": "Add get/set lemmas for `WfRewriter.createOp` (#472)\n\nThe getters we consider are slightly different than the ones we\npreviously had, because there are a few getters that do not make any\nsense to manipulate directly at that level of abstraction (like first\nuses).",
          "timestamp": "2026-04-29T21:17:48Z",
          "tree_id": "fcf6b79e88b5aab9071ee253b0d56ab27226ede4",
          "url": "https://github.com/opencompl/veir/commit/7fbfdd9d4fe8a6c68341f1a4959993bfa3aa8d8a"
        },
        "date": 1777497657601,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2168000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002168s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3273000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003273s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2166000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002166s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2716000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002716s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2137000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002137s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2166000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002166s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1753000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001753s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1793000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001793s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2177000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002177s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4669000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004669s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2151000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002151s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2677000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002677s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2164000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002164s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1802000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001802s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1752000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001752s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1422000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001422s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2134000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002134s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3235000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003235s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1750000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001750s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 10000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000010s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1766000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001766s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 752000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000752s"
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
          "id": "ca1dd404e93e93ac2eb94ab7a36da578bd20b6f1",
          "message": "fix definition of refinement (#479)\n\nThe previous definition of refinement was incorrect, a poison can never\nrefine a concrete value.",
          "timestamp": "2026-04-30T08:33:39Z",
          "tree_id": "40990ec256dc43068fe65ca2d66168d165b89d75",
          "url": "https://github.com/opencompl/veir/commit/ca1dd404e93e93ac2eb94ab7a36da578bd20b6f1"
        },
        "date": 1777538173849,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2296000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002296s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3893000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003893s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2302000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002302s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3252000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003252s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2330000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002330s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2493000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002493s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1930000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001930s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1990000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001990s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2308000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002308s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5424000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005424s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2313000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002313s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3121000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003121s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2297000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002297s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2017000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002017s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1919000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001919s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1580000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001580s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2370000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002370s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3764000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003764s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1955000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001955s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1952000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001952s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 786000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000786s"
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
          "distinct": false,
          "id": "da74b917befb9688e6f959ee222f947c3eca92f0",
          "message": "Split the Rewriter `get-set` lemmas (#478)\n\n`Rewriter/GetSetInBounds.lean` was a bit of a bottleneck when compiling.\nSince most of the lemmas inside it are independent, splitting this file\nimproves compilation time (see the `radar` results).\n\nAlso, rename it to `GetSet.lean`.\n\nThis file has no other changes.",
          "timestamp": "2026-04-30T16:11:44Z",
          "tree_id": "24a869a1b84e07286affc22f04c360b5b348e906",
          "url": "https://github.com/opencompl/veir/commit/da74b917befb9688e6f959ee222f947c3eca92f0"
        },
        "date": 1777566068622,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1932000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001932s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3548000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003548s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1897000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001897s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2910000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002910s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1941000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001941s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2172000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002172s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1572000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001572s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1767000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001767s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1910000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001910s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4902000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004902s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1880000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001880s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2715000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002715s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1886000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001886s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1739000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001739s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1573000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001573s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1373000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001373s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1896000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001896s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3285000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003285s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1566000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001566s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 10000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000010s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1577000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001577s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 748000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000748s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "74881848+nchappe@users.noreply.github.com",
            "name": "nchappe",
            "username": "nchappe"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a7ca683ffdb09c977c10d82796b4b1cc99641776",
          "message": "Parse pretty dialect types (#480)\n\nCurrently only dialect types of the form `!a.b<c>` are supported.\n\nThis adds supports for dialect types of the form `!a.b`.",
          "timestamp": "2026-04-30T16:14:36Z",
          "tree_id": "8fbf1bd7c350f97c2a6001a817390685d97b205a",
          "url": "https://github.com/opencompl/veir/commit/a7ca683ffdb09c977c10d82796b4b1cc99641776"
        },
        "date": 1777566210728,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2139000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002139s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3221000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003221s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2108000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002108s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2650000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002650s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2117000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002117s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2131000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002131s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1732000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001732s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1768000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001768s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2147000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002147s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4539000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004539s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2152000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002152s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2654000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002654s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2125000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002125s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1787000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001787s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1798000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001798s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1456000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001456s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2141000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002141s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3157000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003157s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1746000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001746s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1737000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001737s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 742000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000742s"
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
          "id": "4689da7681854ed1617641a66d7e552d9d4ed289",
          "message": "Parser linearity fix and optimization (#481)\n\nIncreases parser performance by 9.9x in benchmark and likely by a\nmagnitude from time complexity perspective. Original code by @ineol.\n\nRequired by #435.\n\nBenchmarked against\n[`sqlite-3-stripped.mlir`](https://github.com/opencompl/veir/blob/math-fehr/sqlite-test/sqlite3-stripped.mlir)\nfrom `math-fehr` branch. Old commit is\nhttps://github.com/opencompl/veir/commit/da74b917befb9688e6f959ee222f947c3eca92f0\nand new commit is current PR.\n\n```\n> hyperfine \"./old-veir-opt sqlite3-stripped.mlir\" \"./new-veir-opt sqlite3-stripped.mlir\"\nBenchmark 1: ./old-veir-opt sqlite3-stripped.mlir\n  Time (mean ± σ):     22.361 s ±  0.138 s    [User: 22.213 s, System: 0.062 s]\n  Range (min … max):   22.059 s … 22.501 s    10 runs\n\nBenchmark 2: ./new-veir-opt sqlite3-stripped.mlir\n  Time (mean ± σ):      2.259 s ±  0.027 s    [User: 2.225 s, System: 0.028 s]\n  Range (min … max):    2.222 s …  2.298 s    10 runs\n\nSummary\n  ./new-veir-opt sqlite3-stripped.mlir ran\n    9.90 ± 0.13 times faster than ./old-veir-opt sqlite3-stripped.mlir\n```\n\nCo-authored-by: Léo Stefanesco <leo.lveb@gmail.com>",
          "timestamp": "2026-05-01T04:28:33Z",
          "tree_id": "56e7b05cf3b7f40bc5554ab46f16e60caa52dc72",
          "url": "https://github.com/opencompl/veir/commit/4689da7681854ed1617641a66d7e552d9d4ed289"
        },
        "date": 1777609884067,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2281000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002281s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3761000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003761s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2328000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002328s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3088000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003088s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2348000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002348s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2409000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002409s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1933000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001933s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1956000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001956s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2352000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002352s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5305000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005305s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2353000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002353s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3050000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003050s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2340000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002340s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2010000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002010s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2002000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002002s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1550000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001550s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2387000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002387s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3695000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003695s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2050000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002050s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1949000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001949s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 778000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000778s"
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
          "distinct": false,
          "id": "08825380b5c8626638be684b7bf04cb1d4d0eecc",
          "message": "fix: generalized refinement for any width `w`  (#485)\n\nWe generalize the definition of the refinement relation for every width,\nand add support for the notation `⊑`.\n\nThis PR was originally part of #457, from where I am pulling out what is\nseparately upstreamable.",
          "timestamp": "2026-05-01T07:35:19Z",
          "tree_id": "d7c09bb8d79f93f02134a28ba98f4021d6f26dad",
          "url": "https://github.com/opencompl/veir/commit/08825380b5c8626638be684b7bf04cb1d4d0eecc"
        },
        "date": 1777621075157,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2867000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002867s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3790000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003790s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2253000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002253s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3086000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003086s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2329000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002329s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2443000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002443s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1901000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001901s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1950000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001950s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2362000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002362s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5314000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005314s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2821000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002821s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3093000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003093s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 3040000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.003040s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2037000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002037s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2507000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002507s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1620000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001620s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 3104000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.003104s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3790000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003790s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1854000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001854s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1943000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001943s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 773000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000773s"
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
          "id": "fc6d3385697dc9549b2e3ad7a77ea35c89832b14",
          "message": "nightly-2026-05-01 lean nightly update (#488)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-05-01T15:15:33Z",
          "tree_id": "1cde8777df3ff7bf0b89e960735b39511cfbb01c",
          "url": "https://github.com/opencompl/veir/commit/fc6d3385697dc9549b2e3ad7a77ea35c89832b14"
        },
        "date": 1777648676721,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2504000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002504s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3835000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003835s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2361000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002361s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3348000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003348s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2311000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002311s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2674000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002674s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1910000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001910s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2018000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002018s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2312000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002312s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5460000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005460s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2338000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002338s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3111000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003111s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2372000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002372s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2108000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002108s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1900000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001900s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1652000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001652s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2310000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002310s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3869000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003869s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1884000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001884s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1972000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001972s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 788000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000788s"
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
          "id": "ebc71525fa6ff3126c28a122a679d7946d12eb27",
          "message": "Add grind pattern for `ValuePtr.getDefiningOp!` and `InBounds` (#482)\n\nThis was needed in a future PR.",
          "timestamp": "2026-05-01T16:08:57Z",
          "tree_id": "71e57386f625de2ebd4dd34c63e54b46d9d146ea",
          "url": "https://github.com/opencompl/veir/commit/ebc71525fa6ff3126c28a122a679d7946d12eb27"
        },
        "date": 1777652586759,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2384000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002384s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3729000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003729s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2377000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002377s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3174000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003174s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2299000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002299s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2433000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002433s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1928000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001928s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1962000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001962s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2247000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002247s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5339000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005339s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2391000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002391s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3074000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003074s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2345000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002345s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2031000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002031s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1943000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001943s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1567000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001567s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2307000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002307s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3735000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003735s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1902000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001902s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2011000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002011s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 789000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000789s"
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
          "id": "029a76b911a0e8d0ac30f8bb31444430cc49ef27",
          "message": "llvm:`getelementptr` (#486)\n\nWe add the syntax for the `llvm.getelementptr` operation",
          "timestamp": "2026-05-01T18:03:53Z",
          "tree_id": "a594f0559db8dc6911a9d7cb257c3cec488ffbe5",
          "url": "https://github.com/opencompl/veir/commit/029a76b911a0e8d0ac30f8bb31444430cc49ef27"
        },
        "date": 1777658874077,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2289000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002289s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3892000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003892s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2414000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002414s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3315000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003315s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2301000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002301s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2602000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002602s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1901000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001901s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2130000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002130s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2363000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002363s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5626000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005626s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2272000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002272s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3164000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003164s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2382000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002382s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2097000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002097s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1974000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001974s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1628000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001628s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2357000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002357s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3873000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003873s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1971000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001971s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2009000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 886000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000886s"
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
          "id": "0966b9731822b24ad7c77ddde23aa2fad08df7bc",
          "message": "Add get-set lemmas for `getOpType` (#483)\n\nWe should favor the use of `op.getOpType! ctx` instead of `(op.get!\nctx).opType`. This PR changes the get-set lemmas to use `getOpType!`.",
          "timestamp": "2026-05-01T21:30:44Z",
          "tree_id": "15f03925ad706837f6d081368eaf63538acde90e",
          "url": "https://github.com/opencompl/veir/commit/0966b9731822b24ad7c77ddde23aa2fad08df7bc"
        },
        "date": 1777672052322,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2283000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002283s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3815000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003815s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2297000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002297s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3127000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003127s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2243000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002243s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2450000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002450s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1851000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001851s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1946000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001946s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2283000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002283s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5399000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005399s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2289000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002289s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3089000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003089s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2300000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002300s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2035000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002035s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1871000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001871s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1593000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001593s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2319000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002319s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3733000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003733s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1881000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001881s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1918000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001918s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 792000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000792s"
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
          "distinct": false,
          "id": "a3d0093f8c87471c851f867bb7f7f6e9178d74f5",
          "message": "Add a new axiom for dominance, and improve grind pattern (#484)\n\nThe new axiom states that any user of an operation is being strictly\ndominated by it.",
          "timestamp": "2026-05-01T22:22:40Z",
          "tree_id": "a4549575ae73d3a5cf2de37f8fc04f2693bdf24c",
          "url": "https://github.com/opencompl/veir/commit/a3d0093f8c87471c851f867bb7f7f6e9178d74f5"
        },
        "date": 1777674327031,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1867000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001867s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3454000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003454s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1867000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001867s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2864000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002864s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1874000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001874s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2152000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002152s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1570000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001570s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1778000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001778s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1870000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001870s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4860000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004860s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1887000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001887s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2709000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002709s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1961000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001961s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1749000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001749s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1558000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001558s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1392000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001392s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2053000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002053s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3446000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003446s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1577000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001577s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1559000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001559s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 764000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000764s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "georgerennie@gmail.com",
            "name": "George Rennie",
            "username": "georgerennie"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "e3c4ca8817949c1f626b0bf27ceaa410ead667ab",
          "message": "Parse Location attributes (#489)\n\nThis parses MLIR's location attributes of the form `loc(body)` where\nbody is a string with balanced delimiters inside into a LocationAttr.\n\nLocationAttr just stores `body` as a string for now, without trying to\nparse it further.",
          "timestamp": "2026-05-01T22:31:46Z",
          "tree_id": "a8dd32342274d3804d9dc036fe3462407dc5ac69",
          "url": "https://github.com/opencompl/veir/commit/e3c4ca8817949c1f626b0bf27ceaa410ead667ab"
        },
        "date": 1777675729302,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1858000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001858s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3443000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003443s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1839000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001839s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2881000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002881s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1849000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001849s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2160000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002160s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1658000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001658s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1793000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001793s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1849000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001849s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4837000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004837s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1841000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001841s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2726000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002726s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1855000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001855s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1740000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001740s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1564000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001564s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1428000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001428s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1858000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001858s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3352000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003352s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1566000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001566s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1585000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001585s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 769000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000769s"
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
          "distinct": false,
          "id": "65b768d91cf519030f31b1df8b463fcf1934ee4e",
          "message": "Add `OperationPtr.getResultTypes` (#487)\n\nThis helper is useful in the interpreter, and makes it easier to write\nget-set lemmas for high-level rewriting operations.",
          "timestamp": "2026-05-02T05:54:32Z",
          "tree_id": "27d826907c35cae9f3e2c3f26f437edbb87c2297",
          "url": "https://github.com/opencompl/veir/commit/65b768d91cf519030f31b1df8b463fcf1934ee4e"
        },
        "date": 1777702274585,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2262000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002262s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3764000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003764s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2209000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002209s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3078000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003078s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2247000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002247s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2380000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002380s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1836000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001836s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1920000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001920s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2164000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002164s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5220000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005220s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2262000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002262s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2988000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002988s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2129000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002129s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1948000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001948s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1840000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001840s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1522000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001522s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2259000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002259s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3561000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003561s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1784000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001784s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1794000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001794s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 766000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000766s"
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
          "id": "f8b9419ae293008df93ca618a59d94afb0c98e8c",
          "message": "nightly-2026-05-03 lean nightly update (#493)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-05-04T06:24:27Z",
          "tree_id": "bf0414f47e7ae3079382793bdfe0c2cc03a7070e",
          "url": "https://github.com/opencompl/veir/commit/f8b9419ae293008df93ca618a59d94afb0c98e8c"
        },
        "date": 1777876038545,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2301000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002301s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3756000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003756s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2338000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002338s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3140000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003140s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2255000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002255s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2428000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002428s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1918000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001918s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1978000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001978s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2310000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002310s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5371000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005371s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2290000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002290s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3049000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003049s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2286000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002286s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2009000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002009s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1983000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001983s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1575000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001575s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2277000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002277s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3668000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003668s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1908000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001908s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1906000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001906s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 785000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000785s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "siddu.druid@gmail.com",
            "name": "Siddharth",
            "username": "bollu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b0569416cd5865a8e865463ae847432cc676a02d",
          "message": "feat: add unpacked floats (#473)\n\nThis PR adds support for unpacked floating point numbers,\nwhich represent a nonzero rational number as two bitvectors,\nthe exponent and the significand.\n\n---------\n\nCo-authored-by: Luisa Cicolini <48860705+luisacicolini@users.noreply.github.com>\nCo-authored-by: Tobias Grosser <github@grosser.es>",
          "timestamp": "2026-05-04T10:07:09Z",
          "tree_id": "a0f5e2da80d96141722c64adc2d8ff227db0edb5",
          "url": "https://github.com/opencompl/veir/commit/b0569416cd5865a8e865463ae847432cc676a02d"
        },
        "date": 1777889392601,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2252000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002252s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3760000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003760s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2324000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002324s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3135000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003135s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2276000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002276s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2376000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002376s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1828000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001828s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1964000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001964s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2295000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002295s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5307000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005307s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2349000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002349s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3057000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003057s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2192000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002192s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1951000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001951s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1838000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001838s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1552000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001552s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2300000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002300s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3643000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003643s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1905000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001905s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1855000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001855s"
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
            "email": "mathieu.fehr@gmail.com",
            "name": "Mathieu Fehr",
            "username": "math-fehr"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "202f7eceeaf880ff524423fb7c66ddca5a2ee59d",
          "message": "Fix definition of `.WellFormed` to only take pointers instead of structures. (#494)\n\n`Operation.WellFormed`, `Block.WellFormed`, `Region.WellFormed` were\ntaking both the pointer and the structure as argument, despite the\nstructure not being used in any of the fields.\n\nThis changes their names to `OperationPtr.WellFormed` (etc..), and\nremove the structure argument. This doesn't have any other changes.\n\nFixes #44",
          "timestamp": "2026-05-04T15:57:25Z",
          "tree_id": "a0c012bb22cb8a7a18ff70328d28d607be52a043",
          "url": "https://github.com/opencompl/veir/commit/202f7eceeaf880ff524423fb7c66ddca5a2ee59d"
        },
        "date": 1777911072549,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1852000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001852s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3437000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003437s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1864000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001864s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2863000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002863s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1872000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001872s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2161000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002161s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1613000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001613s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1781000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001781s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1853000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001853s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4783000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004783s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1850000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001850s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2730000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002730s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1901000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001901s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1719000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001719s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1559000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001559s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1395000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001395s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1859000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001859s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3247000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003247s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1578000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001578s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1586000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001586s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 769000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000769s"
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
          "id": "3d53c1b50d67a5480c91b3900ccb2d7c1751be80",
          "message": "remove trailing whitespaces in '*.lean' files (#496)",
          "timestamp": "2026-05-04T16:47:04Z",
          "tree_id": "b2d34c2da2503f5daedb61e02e6cb84ca07ff5ac",
          "url": "https://github.com/opencompl/veir/commit/3d53c1b50d67a5480c91b3900ccb2d7c1751be80"
        },
        "date": 1777913386887,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2372000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002372s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3740000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003740s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2188000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002188s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3125000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003125s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2345000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002345s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2424000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002424s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2016000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002016s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1940000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001940s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2323000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002323s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5763000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005763s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2401000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002401s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3051000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003051s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2256000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002256s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2062000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002062s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1889000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001889s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1561000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001561s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2305000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002305s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3731000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003731s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1890000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001890s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1899000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001899s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 802000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000802s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "74881848+nchappe@users.noreply.github.com",
            "name": "nchappe",
            "username": "nchappe"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "9d947684cb2c677dbdf410d0c0abdbcf0f9b774b",
          "message": "Parse RISCV 64-bit load and store (#497)",
          "timestamp": "2026-05-05T01:05:13Z",
          "tree_id": "a4738fc116da017e148b8ebaee3aa14179911df4",
          "url": "https://github.com/opencompl/veir/commit/9d947684cb2c677dbdf410d0c0abdbcf0f9b774b"
        },
        "date": 1777943359446,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2340000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002340s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3801000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003801s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2368000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002368s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3190000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003190s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2379000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002379s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2498000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002498s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2071000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002071s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1999000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001999s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2257000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002257s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5354000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005354s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2316000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002316s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3075000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003075s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2336000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002336s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2013000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002013s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1945000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001945s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1628000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001628s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2312000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002312s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3760000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003760s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1862000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001862s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2012000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002012s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 893000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000893s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "siddu.druid@gmail.com",
            "name": "Siddharth",
            "username": "bollu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "43a96ee3e4b21fae47539939c06d508ab7179c63",
          "message": "feat: Extended Rationals (#495)\n\nThis PR adds the evaluation of packed floating point numbers as extended\nrationals.\nThis allows us to print the value of packed floating point numbers,\nboth to check that our translation from Float → PackedFloat is correct,\nas well as (in a subsequent PR) that our translation from PackedFloat →\nScientificBV is correct.\n\n---------\n\nCo-authored-by: Tobias Grosser <github@grosser.es>\nCo-authored-by: Luisa Cicolini <48860705+luisacicolini@users.noreply.github.com>",
          "timestamp": "2026-05-05T10:01:00Z",
          "tree_id": "fa9aaa3e40bd4909bfaabdb94d85ba1dc1d2228d",
          "url": "https://github.com/opencompl/veir/commit/43a96ee3e4b21fae47539939c06d508ab7179c63"
        },
        "date": 1777976276352,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1887000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001887s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3470000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003470s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1905000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001905s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2947000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002947s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1887000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001887s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2183000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002183s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1596000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001596s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1780000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001780s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1892000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001892s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4867000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004867s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1878000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001878s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2726000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002726s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1890000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001890s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1752000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001752s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1595000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001595s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1391000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001391s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1871000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001871s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3309000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003309s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1592000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001592s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1578000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001578s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 751000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000751s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "siddu.druid@gmail.com",
            "name": "Siddharth",
            "username": "bollu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "fa58d04e4e70cacff4e26bf327f62bc0a0b21b54",
          "message": "fix: open namespace after structure has been defined [FP] (#500)\n\nThis enables dot notation to work properly, and has the structure\nbe scoped as `Veir.Data.FP.X`, followed by a namespace of\n`Veir.Data.FP.X` which allows `X` theory to be developed.",
          "timestamp": "2026-05-05T10:46:03Z",
          "tree_id": "4137d76c17ab6910591f06a8068e2f576e36c58b",
          "url": "https://github.com/opencompl/veir/commit/fa58d04e4e70cacff4e26bf327f62bc0a0b21b54"
        },
        "date": 1777978121241,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1900000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001900s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3414000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003414s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1885000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001885s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2919000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002919s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1890000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001890s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2171000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002171s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1585000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001585s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1798000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001798s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1868000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001868s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4792000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004792s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1872000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001872s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2737000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002737s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1852000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001852s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1753000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001753s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1574000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001574s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1381000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001381s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1873000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001873s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3267000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003267s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1605000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001605s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1590000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001590s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 785000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000785s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "siddu.druid@gmail.com",
            "name": "Siddharth",
            "username": "bollu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "dac9719bb97e2badc1c1350ca4aee92b6b285fce",
          "message": "feat: add extended scientific rational approximations (EScientificBV) for exact FP (#498)\n\nThis adds a new, *non-bitblastable* inductive, `EScientificBV` that\naccurately represents the value of a `PackedFloat` as one of four\nstates: (1) plus minus zero, (2) plus minus infinity, (3) a finite\nnumber, and (4) NaN.\n\nThe design for rounding will be to go from an `ScientificBV unpackedSig\nunpackedExp` to `EScientificBV packedSig packedExp`. Finally, we will\npack the resulting `EScientificBV` up to get a `PackedFloat`.\n\nSo, overall, our operation pipeline for fast simulation of lower\nprecision floats will be of the form:\n\n```lean\n  xinit: FastFloat 3 5 + yinit: FastFloat 3 5 -- input types, isomorphic to float.\n -> x:float + y:float -> z:float  -- carry out operation in full precision\n -> zpacked:PackedFloat -> zunpacked:EScientificBV -- convert to IR \n -> zround:EScientificBV -- round on the IR \n -> zfinal:PackedFloat --recreate IEEEE representation\n -> zresult:float -- cast back into native type\n -> zresult:FastFloat 3 5 -- coerce into FastFloat wrapper.\n```\n\n\nI opt to make it non-bitblastable as it's much easier to read the\nsemantics from this version, which @luisacicolini and @tobiasgrosser\nwould appreciate. Furthermore, we should be able to use the same\napproach as `LLVM.Int` to then expose a bitblastable version that is\nproven isomorphic to this inductive, non-bitblastable version.\n\n---------\n\nCo-authored-by: Tobias Grosser <github@grosser.es>\nCo-authored-by: Luisa Cicolini <48860705+luisacicolini@users.noreply.github.com>",
          "timestamp": "2026-05-05T18:24:23Z",
          "tree_id": "c6f9f4065160a66231cacebec7fd28c1daf566df",
          "url": "https://github.com/opencompl/veir/commit/dac9719bb97e2badc1c1350ca4aee92b6b285fce"
        },
        "date": 1778005623766,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2390000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002390s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3816000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003816s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2284000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002284s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3202000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003202s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2316000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002316s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2527000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002527s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1980000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001980s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 2000000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002000s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2261000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002261s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5419000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005419s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2256000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002256s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3104000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003104s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2351000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002351s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2019000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002019s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2115000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002115s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1604000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001604s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2328000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002328s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3870000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003870s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1971000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001971s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1922000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001922s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 786000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000786s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "siddu.druid@gmail.com",
            "name": "Siddharth",
            "username": "bollu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "b6b654de83641bbe22c714bc434aad7fcfa062d4",
          "message": "feat: add FP state inductive (#502)\n\nThis PR adds a new C-style enum-inductive called 'state' which is\nbitblastable, and enumerates the possible states a floating point number\ncan be in. This will be used to define unpacking, and to redefine the\nrational interpretation of a packed number in a way that allows for\nreasoning across abstraction layers (packed / escientific) of the status\nof a given object.\n\n---------\n\nCo-authored-by: Copilot Autofix powered by AI <175728472+Copilot@users.noreply.github.com>",
          "timestamp": "2026-05-05T21:44:06Z",
          "tree_id": "7a45ecb19cbab069e53e8e1f18e1c88474dc2932",
          "url": "https://github.com/opencompl/veir/commit/b6b654de83641bbe22c714bc434aad7fcfa062d4"
        },
        "date": 1778017616419,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2163000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002163s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3282000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003282s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2140000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002140s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2673000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002673s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2177000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002177s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2155000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002155s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1813000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001813s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1811000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001811s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2205000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002205s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4707000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004707s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2172000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002172s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2683000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002683s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2159000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002159s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1795000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001795s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1780000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001780s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1443000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001443s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2209000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002209s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3259000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003259s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1773000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001773s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1799000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001799s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 753000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000753s"
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
          "id": "428d8b18101ae36d34a53708c311923e94dc5eb3",
          "message": "nightly-2026-05-05 lean nightly update (#506)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-05-06T15:42:33Z",
          "tree_id": "86b5c5563b2e8cd824cf21ee5ec70ce11b9dd17f",
          "url": "https://github.com/opencompl/veir/commit/428d8b18101ae36d34a53708c311923e94dc5eb3"
        },
        "date": 1778082320822,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2416000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002416s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3830000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003830s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2282000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002282s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3183000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003183s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2323000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002323s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2431000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002431s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2023000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002023s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1968000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001968s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2513000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002513s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5340000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005340s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2314000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002314s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3123000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003123s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2367000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002367s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2008000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002008s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1955000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001955s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1571000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001571s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2328000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002328s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3706000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003706s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1988000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001988s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1939000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001939s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 774000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000774s"
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
          "distinct": false,
          "id": "2deed29c9be96e5615f55ed728ea32097c4fa613",
          "message": "Use `WfIRContext` in verifier instead of `IRContext`. (#503)\n\nIt is a bit ugly because we have to add `.raw` everywhere, but this is\nthe current state of `WfIRContext` until I find a good solution, or that\nLean allows to have coercions with metavariables.",
          "timestamp": "2026-05-06T18:30:57Z",
          "tree_id": "91f3abbfb6860e57a57810f6978a624f677d3bee",
          "url": "https://github.com/opencompl/veir/commit/2deed29c9be96e5615f55ed728ea32097c4fa613"
        },
        "date": 1778092434785,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2258000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002258s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3774000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003774s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2314000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002314s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3181000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003181s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2316000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002316s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2442000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002442s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1964000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001964s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1979000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001979s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2307000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002307s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5339000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005339s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2305000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002305s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3108000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003108s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2253000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002253s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1990000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001990s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1914000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001914s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1551000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001551s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2285000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002285s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3723000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003723s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1893000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001893s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1891000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001891s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 763000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000763s"
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
          "id": "51c0ca787084c27453f827b4c62ce523b96bf39d",
          "message": "remove `LLVM.sdiv` redundant poison condition (#507)\n\nIt feels like this condition is checked already in `y' == 0 || (w != 1\n&& x' == (BitVec.intMin w) && y' == -1)` (a couple lines above), so this\nshould be redundant.",
          "timestamp": "2026-05-06T21:36:12Z",
          "tree_id": "2347164a91d76386c94ff4cdd906e2fe642e91f5",
          "url": "https://github.com/opencompl/veir/commit/51c0ca787084c27453f827b4c62ce523b96bf39d"
        },
        "date": 1778103549748,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2368000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002368s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3784000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003784s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2375000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002375s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3181000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003181s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2400000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002400s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2510000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002510s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2115000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002115s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1979000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001979s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2400000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002400s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5368000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005368s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2450000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002450s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3113000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003113s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2403000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002403s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2009000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002009s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1917000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001917s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1550000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001550s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2389000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002389s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3738000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003738s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1961000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001961s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1940000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001940s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 770000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000770s"
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
          "id": "da35205fc1ba70559876941cda0774fa7fea753b",
          "message": "Split interpretOp' by dialect (#512)\n\nThis keeps the sizes of our match statements small and prepares for an\neventual move of these semantics into dialect-specific files.",
          "timestamp": "2026-05-07T06:07:41Z",
          "tree_id": "d3ffba182079d85f8a2b2cddb499f1d1e1f473d0",
          "url": "https://github.com/opencompl/veir/commit/da35205fc1ba70559876941cda0774fa7fea753b"
        },
        "date": 1778134341498,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2523000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002523s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3870000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003870s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2439000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002439s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3204000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003204s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2578000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002578s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2473000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002473s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2058000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002058s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1972000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001972s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2626000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002626s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5315000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005315s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2510000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002510s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3164000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003164s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2524000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002524s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2011000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002011s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2171000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002171s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1556000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001556s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2581000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002581s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3764000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003764s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2233000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002233s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2104000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002104s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 778000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000778s"
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
          "id": "c56ebbdb68bbd534a474466edb855a04567cf07e",
          "message": "Ensure unit-tests fail on io (#511)\n\nIn case unit tests print info or warnings, fail the build. This requires\nus to pass `--iofail` to `lake test`.\n\nAdditionally, this PR disables unit tests to be run while building the\nproject, as they would otherwise be run twice. We prefer to have a\nseparate build step for unit tests, such that failures there are\napparent.",
          "timestamp": "2026-05-07T06:20:54Z",
          "tree_id": "8b3ad89bfaf2e407725ffca21cf5b41ea4de5fd0",
          "url": "https://github.com/opencompl/veir/commit/c56ebbdb68bbd534a474466edb855a04567cf07e"
        },
        "date": 1778135001798,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2373000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002373s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3855000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003855s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2383000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002383s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3203000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003203s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2382000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002382s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2472000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002472s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1926000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001926s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1996000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001996s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2326000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002326s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5394000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005394s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2369000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002369s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3094000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003094s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2294000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002294s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2029000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002029s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1979000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001979s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1581000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001581s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2249000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002249s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3749000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003749s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1857000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001857s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1950000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001950s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 773000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000773s"
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
          "id": "c5ccd9cfb1f2c98fea4595c873ed5ec07d7027b2",
          "message": "add bitblasting test (#499)\n\nWe add to unittest the tests for the bitblastability of the `LLVM.Int`\ntype.\nThe tests come from\n[lean-mlir](https://github.com/opencompl/lean-mlir/blob/main/SSA/Projects/InstCombine/AliveStatements.lean)\nand are instantiated for bitvectors of width 64.\n\nWe also introduce a simp set `llvm_toBitVec`, aimed at unfolding the\nsemantics of `LLVM.Int` operations to bitblastable ones - a call to this\nsimp set + a call to bv_decide should suffice to solve all lemmas on\nfixed-width `LLVM.Int` bitblastable operations.",
          "timestamp": "2026-05-07T10:16:20Z",
          "tree_id": "dad24d9489a9d4c66ae16a16efb50db0238ff844",
          "url": "https://github.com/opencompl/veir/commit/c5ccd9cfb1f2c98fea4595c873ed5ec07d7027b2"
        },
        "date": 1778149138210,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2579000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002579s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3788000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003788s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2307000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002307s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3159000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003159s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2479000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002479s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2513000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002513s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2045000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002045s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1989000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001989s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2578000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002578s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5362000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005362s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2561000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002561s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3076000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003076s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2522000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002522s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 2016000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002016s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2170000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002170s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1586000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001586s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2485000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002485s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3715000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003715s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2034000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002034s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2214000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002214s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 786000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000786s"
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
          "id": "3763f58030a8fb5ead4a199e353bf73911f2c211",
          "message": "nightly-2026-05-07 lean nightly update (#513)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-05-07T15:43:43Z",
          "tree_id": "2aa12dc46c5b75499be16b8f54d10f0a75a4de8d",
          "url": "https://github.com/opencompl/veir/commit/3763f58030a8fb5ead4a199e353bf73911f2c211"
        },
        "date": 1778168790661,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2373000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002373s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3714000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003714s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2380000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002380s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3158000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003158s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2394000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002394s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2383000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002383s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2019000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002019s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1973000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001973s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2570000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002570s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5248000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005248s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2553000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002553s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2979000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002979s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2329000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002329s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1927000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001927s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2114000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002114s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1515000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001515s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2304000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002304s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3735000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003735s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2026000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002026s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2044000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002044s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 755000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000755s"
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
          "id": "79a8f32ea2661b7e99b8792973a9d96b3fa1d14f",
          "message": "Add `IRContext.Verified` and `OperationPtr.Verified` (#509)\n\n`OperationPtr.Verified` asserts that the operation verifies its local\ninvariants, and `IRContext.Verified` asserts that all contained\noperations verify their local invariants.",
          "timestamp": "2026-05-07T16:40:05Z",
          "tree_id": "5da44df8d704a7f75242efa0cf7f2a858befc540",
          "url": "https://github.com/opencompl/veir/commit/79a8f32ea2661b7e99b8792973a9d96b3fa1d14f"
        },
        "date": 1778172186464,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1873000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001873s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3400000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003400s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1824000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001824s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2855000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002855s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1829000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001829s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2131000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002131s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1521000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001521s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1743000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001743s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1834000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001834s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4745000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004745s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1819000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001819s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2659000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002659s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1888000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001888s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1737000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001737s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1570000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001570s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1492000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001492s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2034000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002034s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3383000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003383s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1522000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001522s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1522000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001522s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 750000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000750s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "regehr@cs.utah.edu",
            "name": "John Regehr",
            "username": "regehr"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "04cecc553a065043eae2f4519d007ecdd2df004f",
          "message": "brief example of a C->Veir workflow (#514)\n\nif this is documented upstream, I won't have to keep figuring out where\nin my notes I put this stuff :)",
          "timestamp": "2026-05-07T18:51:46Z",
          "tree_id": "316a24249f4c34498b938be1b80c432ec3b38dd8",
          "url": "https://github.com/opencompl/veir/commit/04cecc553a065043eae2f4519d007ecdd2df004f"
        },
        "date": 1778180068124,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1930000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001930s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3418000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003418s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1823000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001823s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2856000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002856s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1818000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001818s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2111000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002111s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1522000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001522s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1734000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001734s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1829000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001829s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4740000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004740s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1813000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001813s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2671000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002671s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1836000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001836s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1724000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001724s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1539000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001539s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1365000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001365s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1848000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001848s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3191000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003191s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1540000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001540s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1546000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001546s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 741000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000741s"
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
          "id": "046aa309dc104007b9af692bea61d469956082e0",
          "message": "rename llvm.constant to llvm.mlir.constant (#515)\n\nMLIR uses the name `mlir.constant` for the constant operation in the\n`llvm` dialect to indicate that this is an MLIR-specific extension not\npresent in LLVM. LLVM does not have constants as explicit operations in\nthe IR but instead allows constant expressions as separate data\nstructures as an alternative to SSA values.\n\nAs lean does not like `.` in names of inductive cases, we instead use\n`__` as a token for `.`.",
          "timestamp": "2026-05-07T18:59:11Z",
          "tree_id": "9fd594d622069f3100082633de374e76c7bc556f",
          "url": "https://github.com/opencompl/veir/commit/046aa309dc104007b9af692bea61d469956082e0"
        },
        "date": 1778180586334,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2328000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002328s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3754000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003754s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2228000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002228s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3087000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003087s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2263000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002263s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2425000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002425s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1924000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001924s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1973000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001973s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2280000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002280s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5246000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005246s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2231000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002231s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3002000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003002s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2185000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002185s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1945000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001945s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1910000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001910s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1535000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001535s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2250000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002250s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3592000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003592s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1868000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001868s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1788000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001788s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 794000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000794s"
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
          "id": "6b9a726b2cfbf192d7d1aa33ff0b0f470f53910e",
          "message": "Add llvm.func and llvm.module_flags (#516)\n\nWe do not yet support the numerous properties these operations allow\nfor.",
          "timestamp": "2026-05-07T19:25:39Z",
          "tree_id": "613f2d81c309e47b90f08b31d581649944d36ea6",
          "url": "https://github.com/opencompl/veir/commit/6b9a726b2cfbf192d7d1aa33ff0b0f470f53910e"
        },
        "date": 1778182174828,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2018000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002018s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3412000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003412s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1797000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001797s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2848000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002848s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1816000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001816s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2125000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002125s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1572000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001572s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1745000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001745s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1816000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001816s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4686000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004686s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1864000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001864s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2682000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002682s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1830000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001830s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1727000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001727s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1529000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001529s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1382000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001382s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1823000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001823s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3202000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003202s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1567000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001567s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1600000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001600s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 765000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000765s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "regehr@cs.utah.edu",
            "name": "John Regehr",
            "username": "regehr"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c7e14ac49a67aea9e7b593e38b7f9f845e1b0d71",
          "message": "implement the two classic DeMorgan rules and also ~~x -> x (#518)",
          "timestamp": "2026-05-08T00:06:44Z",
          "tree_id": "ccf2d3be3b32946287b4a2b08c62acc67918e3d3",
          "url": "https://github.com/opencompl/veir/commit/c7e14ac49a67aea9e7b593e38b7f9f845e1b0d71"
        },
        "date": 1778198973354,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1593000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001593s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 2682000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002682s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1454000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001454s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2190000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002190s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1414000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001414s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 1625000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001625s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1211000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001211s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1402000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001402s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1410000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001410s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 3631000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003631s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1423000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001423s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2095000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002095s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1431000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001431s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1333000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001333s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1193000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001193s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1073000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001073s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1459000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001459s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 2456000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002456s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1206000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001206s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1180000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001180s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 580000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000580s"
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
          "distinct": false,
          "id": "8bbc62af5cf97b3d3a46ec8828291f5d9419c81d",
          "message": "Add `InsertPoint.atStart` and `InsertPoint.after?` (#524)\n\nThese are two useful methods that were missing",
          "timestamp": "2026-05-08T05:54:55Z",
          "tree_id": "2608b61c39c620c4a9f8c98bdcad6cc4d69656ef",
          "url": "https://github.com/opencompl/veir/commit/8bbc62af5cf97b3d3a46ec8828291f5d9419c81d"
        },
        "date": 1778220372009,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2225000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002225s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3708000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003708s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2207000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002207s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3060000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003060s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2129000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002129s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2335000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002335s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1800000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001800s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1934000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001934s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2126000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002126s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5225000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005225s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2143000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002143s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2942000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002942s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2250000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002250s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1912000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001912s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1786000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001786s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1497000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001497s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2138000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002138s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3546000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003546s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1864000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001864s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1723000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001723s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 765000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000765s"
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
          "id": "bba695ea0f8774c943e014f827af8246dcae4374",
          "message": "Use `BlockPtr.nextArgument` in a lemma (#520)\n\nThis is in general the way we want to define these theorems",
          "timestamp": "2026-05-08T05:55:06Z",
          "tree_id": "239ea1b158d35be25b2b7a017326e79d2fdc771d",
          "url": "https://github.com/opencompl/veir/commit/bba695ea0f8774c943e014f827af8246dcae4374"
        },
        "date": 1778220684105,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2184000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002184s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3641000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003641s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2176000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002176s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3073000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003073s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2219000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002219s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2350000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002350s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1814000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001814s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1924000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001924s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2191000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002191s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5137000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005137s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2235000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002235s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2900000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002900s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2294000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002294s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1922000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001922s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1806000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001806s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1500000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001500s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2169000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002169s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3534000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003534s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1857000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001857s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1821000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001821s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 761000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000761s"
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
          "id": "6527144b403374811e20ee4d5bba28aa0b5d0325",
          "message": "Add two missing simple lemmas about block arguments (#521)",
          "timestamp": "2026-05-08T06:17:22Z",
          "tree_id": "2498eae56da313f2ac22f71b47478b7183028625",
          "url": "https://github.com/opencompl/veir/commit/6527144b403374811e20ee4d5bba28aa0b5d0325"
        },
        "date": 1778222068461,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2229000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002229s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3626000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003626s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2238000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002238s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3032000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003032s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2367000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002367s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2363000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002363s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1945000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001945s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1961000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001961s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2253000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002253s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5230000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005230s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2171000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002171s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2913000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002913s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2358000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002358s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1902000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001902s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1939000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001939s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1548000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001548s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2190000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002190s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3591000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003591s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2003000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002003s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1852000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001852s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 772000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000772s"
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
          "distinct": false,
          "id": "5a835e808f8b620ac30a3a4d6d3eb99ca4b9f761",
          "message": "Add type information in arith.constant and arith.addi verifiers (#510)\n\nThis checks that the operands and result of an `arith.addi` have the\nsame integer type, and that the result of an `arith.constant` has the\nsame type as the property it holds.\n\nAlso, add a lemma that states the constraints of a verified\n`arith.constant` or `arith.addi`. While I would love to have these\nlemmas in `grind`, I do not know how to have a pattern that only\ntriggers if `getOpType! ctx = .arith .addi`. Currently, I can only make\nthis trigger when `getOpType! ctx` is in the context, which is way too\nweak and might trigger this too many times (especially when we are going\nto have more of these lemmas).",
          "timestamp": "2026-05-08T06:29:01Z",
          "tree_id": "1a13d76169a9aae06671477a880a9d36d78c886a",
          "url": "https://github.com/opencompl/veir/commit/5a835e808f8b620ac30a3a4d6d3eb99ca4b9f761"
        },
        "date": 1778222336917,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2216000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002216s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3700000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003700s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2207000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002207s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3091000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003091s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2263000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002263s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2419000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002419s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1827000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001827s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1941000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001941s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2212000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002212s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5228000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005228s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2195000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002195s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2937000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002937s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2154000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002154s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1893000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001893s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1792000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001792s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1510000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001510s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2136000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002136s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3594000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003594s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1883000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001883s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1773000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001773s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 771000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000771s"
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
          "distinct": false,
          "id": "975785d355f496c953748e51c1547f8b4acc6b0a",
          "message": "Add `Rewriter.initBlockArguments` and `Rewriter.pushBlockArguments` (#522)\n\nAlso, add the associated get/set and well-formedness lemmas.\nThese are based on the `Rewriter.initOpResults` ones, and are mostly a\ncopy-paste",
          "timestamp": "2026-05-08T06:29:41Z",
          "tree_id": "e885e06a6c66391b98fb59c9baf4e617c956b74a",
          "url": "https://github.com/opencompl/veir/commit/975785d355f496c953748e51c1547f8b4acc6b0a"
        },
        "date": 1778222564247,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2377000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002377s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3794000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003794s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2266000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002266s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3089000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003089s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2264000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002264s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2424000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002424s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1876000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001876s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1916000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001916s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2174000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002174s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5319000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005319s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2233000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002233s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3032000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003032s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2241000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002241s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1898000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001898s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1915000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001915s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1506000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001506s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2238000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002238s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3685000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003685s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1954000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001954s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1986000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001986s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 782000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000782s"
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
          "id": "5606426a2188a180321cb7a46708ff6b578b2ca1",
          "message": "parseOptionalOp linearity fix (#526)\n\nMissed by #481, required by #523.\n\nCurrent `parseOptionalOp` doesn't have linearity issues but it achieves\nthis by manually resetting the context with `setContext\nInhabited.default` in the middle of modifying the context, which is\nconfusing. In #481, the rest of the parser has migrated over to\n`modifyContext` helpers to achieve linearity while being easier to\nunderstand. `parseOptionalOp` was forgotten in #481, hence this PR is\ncreated to migrate `parseOptionalOp` to use `modifyContextM'`. This way\nthe code is both consistent with the rest of the parser and also easier\nto read.",
          "timestamp": "2026-05-08T06:35:04Z",
          "tree_id": "33f0fbaa253c85fffc7041816740104bc0ec1902",
          "url": "https://github.com/opencompl/veir/commit/5606426a2188a180321cb7a46708ff6b578b2ca1"
        },
        "date": 1778222700280,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2184000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002184s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3612000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003612s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2216000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002216s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3174000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003174s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2236000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002236s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2383000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002383s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1851000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001851s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1917000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001917s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2222000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002222s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5210000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005210s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2248000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002248s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2914000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002914s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2128000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002128s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1886000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001886s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1867000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001867s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1532000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001532s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2138000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002138s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3649000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003649s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1823000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001823s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1785000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001785s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 763000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000763s"
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
          "id": "85c9e72247cf438d804e9cb3c5d90fa5a47f9293",
          "message": "Migrate parser to use WfIRContext (#523)\n\nRequired by #435. Makes writing proofs in verified parser much easier.",
          "timestamp": "2026-05-08T07:00:45Z",
          "tree_id": "ae5c01daa11ea1111e4f938770d2774d7761474d",
          "url": "https://github.com/opencompl/veir/commit/85c9e72247cf438d804e9cb3c5d90fa5a47f9293"
        },
        "date": 1778223814143,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2173000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002173s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3714000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003714s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2195000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002195s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3111000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003111s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2181000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002181s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2378000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002378s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1832000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001832s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1917000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001917s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2218000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002218s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5238000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005238s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2336000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002336s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2984000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002984s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2141000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002141s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1879000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001879s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1853000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001853s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1498000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001498s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2203000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002203s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3618000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003618s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1869000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001869s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1714000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001714s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 752000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000752s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "siddu.druid@gmail.com",
            "name": "Siddharth",
            "username": "bollu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "45c711597701b07a7852a58ad555c92449482126",
          "message": "feat: add EDyadic for computable FP (#505)\n\nAs discussed with @tobiasgrosser, for computable rounding,\nit suffices to use the dyadics as a representation,\nsince it is a compressed, arbitrary-precision representation of numbers\nof the form `k/2^n` where `k` is not divisible by `2`.\n\nTherefore, we add an `EDyadic` type, and show how to convert it to a\nrational. As the next step, we will show how to convert a `PackedFloat`\ninto\nan `EDyadic`.\n\n\nPart of https://github.com/opencompl/veir/issues/504\n\n---------\n\nCo-authored-by: Luisa Cicolini <48860705+luisacicolini@users.noreply.github.com>",
          "timestamp": "2026-05-08T08:05:43Z",
          "tree_id": "687764b03c0d4b31fdfea320919700e087c7f2fe",
          "url": "https://github.com/opencompl/veir/commit/45c711597701b07a7852a58ad555c92449482126"
        },
        "date": 1778227691726,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2151000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002151s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3628000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003628s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2207000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002207s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3072000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003072s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2129000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002129s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2364000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002364s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1818000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001818s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1912000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001912s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2187000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002187s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5192000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005192s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2267000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002267s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2932000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002932s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2131000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002131s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1880000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001880s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1787000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001787s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1478000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001478s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2080000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002080s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3542000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003542s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1786000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001786s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1910000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001910s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 798000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000798s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "siddu.druid@gmail.com",
            "name": "Siddharth",
            "username": "bollu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "96ef196b6e3cdf8a77162c293316258bda4c485e",
          "message": "feat: implement PackedFloat.toEDyadic (#528)\n\nThis PR implements `PackedFloat.toEDyadic`, which interprets a\n`PackedFloat` as an extended dyadic number. This will be used to\nimplement rounding, where the rounder will inspect the exponent and\nvalue of the extended dyadic number in order to then round to the\nclosest packed-bit-representable value.\n\n---------\n\nCo-authored-by: Tobias Grosser <tobias@grosser.es>\nCo-authored-by: Tobias Grosser <github@grosser.es>",
          "timestamp": "2026-05-08T11:40:03Z",
          "tree_id": "f573f6fa2eba24c814c71a9098e69179220e1811",
          "url": "https://github.com/opencompl/veir/commit/96ef196b6e3cdf8a77162c293316258bda4c485e"
        },
        "date": 1778240562423,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2069000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002069s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3635000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003635s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2142000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002142s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3041000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003041s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2211000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002211s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2389000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002389s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1785000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001785s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1915000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001915s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2211000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002211s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5207000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005207s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2224000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002224s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2917000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002917s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2194000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002194s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1941000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001941s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1802000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001802s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1500000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001500s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2308000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002308s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3639000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003639s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1877000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001877s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1804000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001804s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 770000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000770s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "john.regehr@gmail.com",
            "name": "John Regehr",
            "username": "regehr"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "0d051a6b07397698c97f079c0403df93c2dd81ec",
          "message": "support GEPs with more than one index (#532)\n\nwe were not supporting GEPs that do multi-dimensional indexing, this\nadds support for that",
          "timestamp": "2026-05-08T16:44:31Z",
          "tree_id": "0ea8307241e2c77d097eb3f5946222dde1865d8a",
          "url": "https://github.com/opencompl/veir/commit/0d051a6b07397698c97f079c0403df93c2dd81ec"
        },
        "date": 1778258865514,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2237000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002237s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3695000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003695s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2131000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002131s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3099000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003099s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2222000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002222s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2422000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002422s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1868000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001868s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1946000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001946s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2207000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002207s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5246000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005246s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2310000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002310s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2961000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002961s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2148000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002148s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1899000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001899s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1853000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001853s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1506000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001506s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2269000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002269s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3688000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003688s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1935000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001935s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1819000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001819s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 770000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000770s"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "john.regehr@gmail.com",
            "name": "John Regehr",
            "username": "regehr"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "4ee1ff0608bf35180c81c8de65f6978acccd9224",
          "message": "Add FlatSymbolRefAttr (#533)\n\nok this is a revised version of #525 that only adds support for\nFlatSymbolRefAttr! I believe I've addressed all feedback!",
          "timestamp": "2026-05-08T21:40:26Z",
          "tree_id": "803016f562526258eccf5a92b3cb1f74135a1bfc",
          "url": "https://github.com/opencompl/veir/commit/4ee1ff0608bf35180c81c8de65f6978acccd9224"
        },
        "date": 1778277474299,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1841000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001841s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3412000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003412s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1870000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001870s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2874000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002874s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1828000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001828s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2199000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002199s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1530000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001530s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1732000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001732s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1825000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001825s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4686000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004686s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1869000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001869s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2679000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002679s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1865000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001865s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1721000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001721s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1553000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001553s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1368000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001368s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1841000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001841s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3183000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003183s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1528000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001528s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1523000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001523s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 752000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000752s"
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
          "id": "1b8c8ccb05c91adef96e05919439570c43c62bf7",
          "message": "Improve inBounds lemmas for BlockPtr.setArguments (#527)\n\nThe previous implementation was too restrictive and was requiring the\nnew arguments to be larger than the old ones",
          "timestamp": "2026-05-08T21:44:54Z",
          "tree_id": "d1cbc56fe892e48fcd8e9a22e954c431f67bc735",
          "url": "https://github.com/opencompl/veir/commit/1b8c8ccb05c91adef96e05919439570c43c62bf7"
        },
        "date": 1778277743860,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1813000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001813s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3402000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003402s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1827000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001827s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2823000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002823s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1805000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001805s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2104000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002104s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1534000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001534s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1737000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001737s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1811000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001811s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4706000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004706s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1824000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001824s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2675000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002675s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1860000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001860s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1723000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001723s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1517000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001517s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1380000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001380s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1816000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001816s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3218000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003218s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1580000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001580s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 12000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000012s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1529000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001529s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 750000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000750s"
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
          "id": "2bc73e46bbee4c8f8dcba9ebed07b5f16090d998",
          "message": "Add more theorems about `default` values of IR (#536)\n\nThese theorems can be useful sometimes when writing lemmas that works\nwether or not the components are in bounds.",
          "timestamp": "2026-05-09T05:45:48Z",
          "tree_id": "c15c61053f08a7e9084760285079d267a4ba1dcb",
          "url": "https://github.com/opencompl/veir/commit/2bc73e46bbee4c8f8dcba9ebed07b5f16090d998"
        },
        "date": 1778306580893,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2266000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002266s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3667000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003667s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2135000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002135s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3132000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003132s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2200000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002200s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2369000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002369s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1831000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001831s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1987000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001987s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2186000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002186s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5203000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005203s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2245000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002245s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2982000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002982s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2214000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002214s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1905000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001905s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1819000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001819s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1494000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001494s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2286000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002286s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3699000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003699s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1826000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001826s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 7000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000007s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1837000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001837s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 818000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000818s"
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
          "id": "0a0b0abc53ef6c83cbb6f76994cb053b1a8a8fd9",
          "message": "Add one missing get-set lemma for `BlockPtr.setArguments` (#537)",
          "timestamp": "2026-05-09T05:59:41Z",
          "tree_id": "8e23c4cb0c6d45a055e7b221c09187dc8bdf4c26",
          "url": "https://github.com/opencompl/veir/commit/0a0b0abc53ef6c83cbb6f76994cb053b1a8a8fd9"
        },
        "date": 1778307371836,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2082000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002082s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3711000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003711s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2242000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002242s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3139000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003139s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2268000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002268s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2376000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002376s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1848000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001848s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1959000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001959s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2127000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002127s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5263000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005263s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2166000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002166s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2978000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002978s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2132000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002132s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1870000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001870s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1868000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001868s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1508000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001508s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2225000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002225s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3591000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003591s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1883000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001883s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1824000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001824s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 770000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000770s"
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
          "id": "32c4ddf2619742a2b64488598e3e17495425bb2f",
          "message": "Add `Rewriter.initBlockArguments_inBounds` (#538)\n\nThis theorem is quite complex, so we specialize it only in the case what\ninterest us (where `n = 0`). This required improving the definition of\n`Rewriter.pushBlockArgument_inBounds`",
          "timestamp": "2026-05-09T06:12:53Z",
          "tree_id": "31f58d465acc7a5cb809f463e017a9f7a07c7056",
          "url": "https://github.com/opencompl/veir/commit/32c4ddf2619742a2b64488598e3e17495425bb2f"
        },
        "date": 1778307937941,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2194000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002194s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3736000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003736s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2206000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002206s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3098000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003098s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2224000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002224s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2350000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002350s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1822000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001822s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1957000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001957s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2134000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002134s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5163000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005163s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2162000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002162s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2932000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002932s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2205000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002205s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1879000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001879s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1842000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001842s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1501000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001501s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2163000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002163s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3588000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003588s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1889000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001889s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1868000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001868s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 768000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000768s"
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
          "distinct": false,
          "id": "705d63f3cbc53a8320b2af27c6dc00393d402c71",
          "message": "Add two lemmas about first use of values in a well-formed context (#540)\n\nThese lemmas already existed when having a `ValuePtr.DefUse` hypothesis,\nbut they are here defined whenever we have `IRContext.WellFormed`.",
          "timestamp": "2026-05-09T08:01:44Z",
          "tree_id": "b7764ecd9de7601d67530d4819e378cb1e34be17",
          "url": "https://github.com/opencompl/veir/commit/705d63f3cbc53a8320b2af27c6dc00393d402c71"
        },
        "date": 1778314550984,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2317000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002317s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3767000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003767s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2631000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002631s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3141000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003141s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2602000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002602s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2388000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002388s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2249000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002249s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1951000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001951s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2663000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002663s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5297000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005297s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2583000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002583s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2946000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002946s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2636000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002636s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1907000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001907s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2092000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002092s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1472000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001472s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2478000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002478s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3735000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003735s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2161000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002161s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2132000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002132s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 768000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000768s"
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
          "id": "e729cda4ecf4f81314833f53ff7b8955470f2f62",
          "message": "Use runtime checks for WellFormed preconditions in parser (#435)\n\nThis is the first step towards a `sorry`-less parser. The difficult part\nof making the parser `sorry`-less is to prove that the `IRContext` is\n`WellFormed` at all times, which normally requires carrying around the\nproof of the `InBounds` of blocks, operands, regions, insertion points,\netc., at all times in the parser. While these proofs are possible to\nprove directly, doing this likely requires very complicated changes to\nthe parser and/or the addition of many helper lemmas that definitely\ndon't fit within a single PR.\n\nInstead, the approach is to start with only runtime checks and migrate\nto direct proofs one step at a time. Right now, instead of carrying\n`InBounds` proofs with us all the time, we use runtime checks to\nconstruct proofs that things are `InBounds` only when we need them to\nprove `WellFormed` of `IRContext` (runtime checks are possible because\nall the `XXX.InBounds` are `Decidable`). Then, we can gradually swap out\nthe runtime checks with direct proofs as we add more helper lemmas and\nas I understand how to utilize all the nice properties that\n`WfIRContext` provides. Note that the parser remains `sorry`-less\nthroughout this entire process; the only difference is whether the\n`InBounds` proofs are proved directly or checked at runtime using\n`Decidable`.\n\nThe only thing remaining that's making the parser not `sorry`-less is\nthe lack of some helper lemmas for proving `WellFormed` of `IRContext`,\nwhich @math-fehr is working on. This will also be addressed in future\nPRs. This PR is just to setup the runtime check infrastructure and make\nthe parser use it.\n\nI have benchmarked that runtime checks only makes the parser ~5% slower\non super large MLIR files, which is within the acceptable range to me.\nThe benchmark below compares between this PR and current HEAD\n(1b8c8ccb).\n```\n> hyperfine -w 2 \"./old-veir-opt sqlite3-stripped.mlir\" \"./runtime-checks-veir-opt sqlite3-stripped.mlir\"\nBenchmark 1: ./old-veir-opt sqlite3-stripped.mlir\n  Time (mean ± σ):      2.209 s ±  0.020 s    [User: 2.186 s, System: 0.020 s]\n  Range (min … max):    2.180 s …  2.247 s    10 runs\n\nBenchmark 2: ./runtime-checks-veir-opt sqlite3-stripped.mlir\n  Time (mean ± σ):      2.351 s ±  0.015 s    [User: 2.331 s, System: 0.017 s]\n  Range (min … max):    2.326 s …  2.371 s    10 runs\n\nSummary\n  ./old-veir-opt sqlite3-stripped.mlir ran\n    1.06 ± 0.01 times faster than ./runtime-checks-veir-opt sqlite3-stripped.mlir\n```",
          "timestamp": "2026-05-10T03:09:24Z",
          "tree_id": "1de5cddb83da6c41224bd8a262f4fc9ca1abc221",
          "url": "https://github.com/opencompl/veir/commit/e729cda4ecf4f81314833f53ff7b8955470f2f62"
        },
        "date": 1778382745400,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 1818000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001818s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3399000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003399s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 1801000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001801s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 2863000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002863s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 1824000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001824s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2122000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002122s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1520000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001520s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1725000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001725s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 1813000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001813s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 4753000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.004753s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 1825000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001825s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2670000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002670s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 1845000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001845s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1727000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001727s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1521000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001521s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1372000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001372s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 1837000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001837s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3187000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003187s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1523000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001523s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 9000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000009s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1501000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.001501s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 742000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000742s"
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
          "id": "bae4de138b01785d32cb52b7c8f048c02b25c7dd",
          "message": "nightly-2026-05-10 lean nightly update (#541)\n\nautomatic update of lean via GitHub action.\n\nCo-authored-by: github-merge-queue <118344674+github-merge-queue@users.noreply.github.com>",
          "timestamp": "2026-05-10T15:15:41Z",
          "tree_id": "8f016ca1647badec82b597cc72d4682e6a9a05cd",
          "url": "https://github.com/opencompl/veir/commit/bae4de138b01785d32cb52b7c8f048c02b25c7dd"
        },
        "date": 1778426294193,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2630000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002630s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3796000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003796s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2571000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002571s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3107000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003107s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2554000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002554s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2377000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.002377s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 2287000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002287s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1987000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001987s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2623000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002623s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5369000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.005369s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2561000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002561s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 3010000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003010s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2609000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002609s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1927000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001927s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 2285000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002285s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1549000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.001549s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2547000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002547s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3830000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.003830s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 2171000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002171s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 2245000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_create=0.002245s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 898000,
            "unit": "ns",
            "extra": "count=1000 pc=100 iterations=5 median_rewrite=0.000898s"
          }
        ]
      }
    ]
  }
}