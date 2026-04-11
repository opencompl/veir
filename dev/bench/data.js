window.BENCHMARK_DATA = {
  "lastUpdate": 1775933134277,
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
      }
    ]
  }
}