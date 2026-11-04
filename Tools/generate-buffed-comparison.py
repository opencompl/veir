#!/usr/bin/env python3
"""Collect serial cross-backend timings and render a dependency-free HTML report.

Existing report data can be rendered again with --render DATA.json.
Only 100% eligibility is compared: the dense generators select partial-percentage
operations in different orders. MLIR has no sparse generator in this harness.
"""
import argparse
import csv
import datetime as dt
import hashlib
import html
import json
import math
from pathlib import Path
import re
import shutil
import statistics
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
CASES = [
    ("add-fold-forwards", "Constant folding"),
    ("add-zero-forwards", "Zero folding"),
    ("add-zero-reuse-forwards", "Shared-constant zero folding"),
    ("mul-two-forwards", "Multiply-by-two reduction"),
    ("add-fold-forwards-sparse", "Sparse constant folding"),
    ("add-zero-forwards-sparse", "Sparse zero folding"),
    ("mul-two-forwards-sparse", "Sparse multiply reduction"),
    ("add-zero-reuse-first", "First zero fold · single use"),
    ("add-zero-lots-of-reuse-first", "First zero fold · many uses"),
]
COLORS = {"buffered": "#36d7b7", "veir": "#7d9dff", "mlir": "#ffb86b"}
LABELS = {"buffered": "Buffered VeIR · raw results", "veir": "Baseline VeIR · unbuffered", "mlir": "MLIR"}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def command_output(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def quantile(xs, p):
    ys = sorted(xs)
    i = (len(ys) - 1) * p
    lo, hi = math.floor(i), math.ceil(i)
    return ys[lo] + (ys[hi] - ys[lo]) * (i - lo)


def summarize(rows):
    groups = {}
    for row in rows:
        if not row["warmup"]:
            for phase in ("create", "rewrite"):
                groups.setdefault((row["case"], row["n"], row["tool"], phase), []).append(row[phase + "_ms"])
    return [dict(case=c, n=n, tool=t, phase=p, count=len(xs), median=statistics.median(xs),
                 q25=quantile(xs, .25), q75=quantile(xs, .75), minimum=min(xs), maximum=max(xs),
                 cv=100 * statistics.stdev(xs) / statistics.mean(xs) if len(xs) > 1 and statistics.mean(xs) else 0)
            for (c, n, t, p), xs in groups.items()]


def collect(args):
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if (out / "data.json").exists() or (out / "runs.jsonl").exists():
        raise SystemExit(f"Refusing to overwrite measurements in {out}; choose another --output")
    if args.cpu not in __import__("os").sched_getaffinity(0):
        raise SystemExit(f"CPU {args.cpu} is not available")
    paths = {"buffered": ROOT / ".lake/build/bin/buffed-benchmark",
             "veir": ROOT / ".lake/build/bin/run-benchmarks",
             "mlir": args.evaluation.resolve() / "llvm-project/build/bin/test-buffed"}
    snapshots = Path(tempfile.mkdtemp(prefix="buffed-cross-backend-binaries-"))
    binaries = {}
    for tool, path in paths.items():
        if not path.is_file():
            raise SystemExit(f"Missing executable: {path}")
        dest = snapshots / tool
        shutil.copy2(path, dest)
        binaries[tool] = dict(path=str(path), snapshot=str(dest), sha256=sha(dest), label=LABELS[tool])
    llvm = args.evaluation.resolve() / "llvm-project"
    cache = (llvm / "build/CMakeCache.txt").read_text()
    cache_fields = dict(re.findall(r"^(CMAKE_BUILD_TYPE|CMAKE_CXX_FLAGS_RELEASE|LLVM_ENABLE_LTO|LLVM_ENABLE_ASSERTIONS):[^=]+=(.*)$", cache, re.M))
    compiler_files = list((llvm / "build/CMakeFiles").glob("*/CMakeCXXCompiler.cmake"))
    compiler_versions = [re.findall(r'set\(CMAKE_CXX_COMPILER_VERSION "([^"]+)"\)', p.read_text()) for p in compiler_files]
    data = dict(schema=1, collected_at=dt.datetime.now(dt.timezone.utc).isoformat(),
                cases=[dict(id=c, label=l) for c, l in CASES], sizes=args.sizes, percent=100,
                samples=args.samples, warmups=args.warmups, cpu=args.cpu, binaries=binaries,
                veir_parent=command_output(["git", "rev-parse", "HEAD"]),
                veir_diff_sha256=hashlib.sha256(subprocess.check_output(["git", "diff", "--binary"], cwd=ROOT)).hexdigest(),
                mlir_checkout=command_output(["git", "rev-parse", "HEAD"], llvm),
                mlir_checkout_status=command_output(["git", "status", "--short"], llvm),
                mlir_build=cache_fields, mlir_compiler_versions=compiler_versions,
                machine=command_output(["uname", "-a"]),
                cpu_model=next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("model name")), "unknown"),
                lean_version=command_output(["lake", "env", "lean", "--version"]),
                lean_build="Release, -O3 -DNDEBUG -flto=full; Tools/lean-clang",
                source_hashes={str(p.relative_to(ROOT)): sha(p) for p in [ROOT / "BuffedBenchmark.lean", ROOT / "Veir/Benchmarks.lean", ROOT / "Exe/RunBenchmarks.lean"]},
                mlir_source_sha256=sha(llvm / "mlir/tools/test-buffed/test-buffed.cpp"),
                rows=[])
    timing = {p: re.compile(rf"{p} time \(s\):\s*([0-9.+eE-]+)") for p in ("create", "rewrite")}
    start = time.monotonic()
    with (out / "runs.jsonl").open("w") as logs:
        for case_index, (case, _) in enumerate(CASES):
            tools = ["buffered", "veir"] + ([] if "sparse" in case else ["mlir"])
            for size_index, n in enumerate(args.sizes):
                print(f"{case}: n={n}, {', '.join(tools)}", flush=True)
                for round_index in range(args.warmups + args.samples):
                    # Rotate the first runner; measured rounds start a fresh balanced cycle.
                    sample = round_index - args.warmups
                    rotation = (sample + case_index + size_index) % len(tools)
                    order = tools[rotation:] + tools[:rotation]
                    for position, tool in enumerate(order):
                        cmd = ["taskset", "-c", str(args.cpu), binaries[tool]["snapshot"], case, str(n), "100"]
                        begun = time.monotonic()
                        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=args.timeout)
                        text = proc.stdout + "\n" + proc.stderr
                        record = dict(case=case, n=n, percent=100, tool=tool, sample=sample,
                                      warmup=sample < 0, order=position, returncode=proc.returncode,
                                      wall_s=time.monotonic() - begun)
                        logs.write(json.dumps(dict(record, command=cmd, stdout=proc.stdout, stderr=proc.stderr)) + "\n")
                        logs.flush()
                        if proc.returncode:
                            raise RuntimeError(f"Failed {cmd}: {proc.returncode}; see runs.jsonl")
                        for phase, regex in timing.items():
                            matches = regex.findall(text)
                            if len(matches) != 1:
                                raise RuntimeError(f"Expected exactly one {phase} timing for {cmd}: {matches}")
                            value = float(matches[0]) * 1000
                            if not math.isfinite(value) or value < 0:
                                raise RuntimeError(f"Invalid timing: {value}")
                            record[phase + "_ms"] = value
                        data["rows"].append(record)
    data["elapsed_s"] = time.monotonic() - start
    data["summary"] = summarize(data["rows"])
    expected = sum((2 if "sparse" in c else 3) for c, _ in CASES) * len(args.sizes) * (args.samples + args.warmups)
    assert len(data["rows"]) == expected
    assert all(s["count"] == args.samples for s in data["summary"])
    (out / "data.json").write_text(json.dumps(data, indent=2) + "\n")
    with (out / "samples.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(data["rows"][0]))
        writer.writeheader()
        writer.writerows(data["rows"])
    return data


PAGE = r'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Buffered VeIR · VeIR · MLIR | Native benchmark report</title>
<style>
:root{color-scheme:dark;--bg:#0b1220;--panel:#131e30;--ink:#e7eef9;--muted:#a1b1c9;--line:#29384e;--green:#36d7b7}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.55 system-ui,sans-serif}main{max-width:1380px;margin:auto;padding:48px 28px}h1{font-size:clamp(30px,4vw,52px);line-height:1.15;letter-spacing:-1.5px;margin:12px 0 20px}h2{margin-top:38px}h3{margin:0;font-size:17px}.eyebrow{color:var(--green);letter-spacing:2px;font-size:12px;font-weight:700;text-transform:uppercase}.subtitle{max-width:890px;color:var(--muted);font-size:17px}.chips,.legend,.controls{display:flex;flex-wrap:wrap;gap:12px;align-items:center}.chips span{border:1px solid var(--line);padding:5px 12px;border-radius:30px;color:var(--muted);font-size:13px}.notice{border-left:3px solid #ffb86b;background:#25231f;padding:14px 20px;margin:26px 0;color:#f6dfbe}.controls{background:var(--panel);padding:16px;border:1px solid var(--line);border-radius:12px;margin-top:24px}select,button{background:#1e2b43;color:var(--ink);border:1px solid #415570;padding:8px 12px;border-radius:7px;font:inherit;cursor:pointer}label{display:flex;align-items:center;gap:8px}.legend{margin:20px 0}.key{display:inline-block;width:11px;height:11px;border-radius:50%;margin-right:7px}.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:20px}.card{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:20px}.card p{font-size:13px;color:var(--muted);margin:7px 0 0}.plot{width:100%;height:auto;display:block}.plot text{font-family:system-ui,sans-serif;fill:var(--muted);font-size:11px}.plot .title{fill:var(--ink)}.tablewrap{overflow:auto;border:1px solid var(--line);border-radius:10px}table{border-collapse:collapse;width:100%;font-size:13px}th,td{padding:12px;text-align:right;border-bottom:1px solid var(--line);white-space:nowrap}th:first-child,td:first-child{text-align:left}thead{background:#1e2b43}td small{color:var(--muted);display:block}details{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:18px;margin:16px 0}summary{cursor:pointer;font-weight:650}li{margin:9px 0}code{font-size:12px;overflow-wrap:anywhere;white-space:normal}a{color:var(--green)}.muted{color:var(--muted)}.note{font-size:13px;color:var(--muted)}footer{margin-top:36px;color:var(--muted);font-size:12px}.downloads{display:flex;gap:10px;margin:18px 0}@media(max-width:800px){main{padding:26px 14px}.grid{grid-template-columns:1fr}.card{padding:12px}}
</style></head><body><main>
<div class="eyebrow">Native performance / raw-result generation</div>
<h1>Buffered VeIR vs.<br>baseline VeIR &amp; MLIR</h1>
<p class="subtitle">Fresh serial measurements of construction and rewriting. Buffered VeIR uses the new raw-result <code>buffed</code> generator; baseline VeIR is the current unbuffered backend, not the earlier direct-Erased buffered implementation.</p>
<div class="chips" id="chips"></div>
<div class="notice">Cross-implementation comparison, not an isolated compiler experiment. Lean uses full LTO; the existing MLIR Release build has LTO off. Only 100% eligibility is shown. MLIR does not implement the sparse workloads in this harness.</div>
<div class="controls"><label>Phase <select id="phase"><option value="rewrite">Rewriting</option><option value="create">Construction</option></select></label><label>Table / ratios at n <select id="size"></select></label><label><input id="log" type="checkbox"> Log time axis</label></div>
<div class="legend" id="legend"></div>
<p class="note">Lines show medians; whiskers show the interquartile range (25th–75th percentile), not confidence intervals. Hover over a point for its timing, spread, and CV. The x axis is logarithmic in generator size n, not total IR operation count. Lower time is better.</p>
<div class="grid" id="plots"></div>
<h2 id="tableTitle">Detailed comparison</h2><p class="note">Ratios are baseline time ÷ buffered time: above 1× favors buffered VeIR; below 1× favors the baseline. Timings below 0.010 ms are marked †: microsecond quantization and fixed overhead make their ratios unreliable.</p>
<div class="tablewrap"><table><thead><tr><th>Benchmark</th><th>Buffered · ms</th><th>VeIR · ms</th><th>MLIR · ms</th><th>VeIR / buffered</th><th>MLIR / buffered</th></tr></thead><tbody id="table"></tbody></table></div>
<h2>Method &amp; provenance</h2>
<details open><summary>What is—and is not—being compared</summary><ul>
<li>The workload names and phase timers follow <code>../buffed-evaluation/run_benchmarks.py</code>. Its historical CSV was <strong>not</strong> mixed into this report: that runner uses 15 concurrent workers, unlike these fresh serial measurements.</li>
<li>The evaluation checkout's <code>buffed/</code> VeIR submodule is empty. Baseline VeIR therefore uses this repository's <code>.lake/build/bin/run-benchmarks</code>, the merged, unbuffered VeIR backend. It is <strong>not</strong> a reproduction of the evaluation's historical ChainMail revision.</li>
<li>Buffered and baseline VeIR use the current Lean build. MLIR uses the available <code>llvm-project/build/bin/test-buffed</code> executable in the evaluation checkout; it was not rebuilt for this run. Its recorded source checkout and CMake configuration are supplied below, along with the exact binary hash.</li>
<li>All tools receive identical benchmark names, n, and 100% eligibility. Dense generators choose partially eligible operations in different orders, so 1%/10% workloads are deliberately omitted. Backend representations and scaffolding differ; the inputs are corresponding generated workloads, not byte-identical serialized IR.</li>
<li>Sparse workloads compare the two VeIR backends only. No MLIR number is inferred or plotted as zero. Worklist rewrites are omitted because the buffered harness provides forward traversal only.</li>
<li>Creation and rewrite times come from each executable's internal timers. Process initialization, final IR printing, and final teardown are not included. Binary processes run sequentially and finish before the next starts.</li>
<li>For every size/case/backend: two discarded warmups, nine measured runs by default. Backend order rotates across rounds. No samples are trimmed. Affinity is fixed; the rest of the machine is not isolated and turbo/governor settings are unchanged. No builds, tests, or profiling run concurrently.</li>
<li>These are benchmark harnesses, not a new correctness verification of each benchmark program; existing proof placeholders in the Lean benchmark sources remain. The generator's production proof audits are separate.</li>
</ul></details>
<details><summary>Build identity, hashes, and environment</summary><div id="provenance"></div></details>
<div class="downloads"><button id="downloadJson">Download embedded data · JSON</button><button id="downloadCsv">Download all samples · CSV</button></div>
<p class="note">This HTML contains its plot code and measurement data. It needs no network connection or external JavaScript libraries.</p>
<noscript><div class="notice">Enable JavaScript to view interactive plots. The accompanying data.json and samples.csv contain the complete measurements.</div></noscript>
<footer id="footer"></footer>
</main><script id="report-data" type="application/json">__DATA__</script>
<script>
'use strict';
const D=JSON.parse(document.getElementById('report-data').textContent);
const colors=__COLORS__,labels=__LABELS__;
const E=s=>String(s).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;').replaceAll('"','&quot;');
const fmt=x=>x===0?'0':x>=100?x.toFixed(1):x>=1?x.toFixed(3):x.toPrecision(3);
const lookup=new Map(D.summary.map(r=>[[r.case,r.n,r.tool,r.phase].join('|'),r]));
const get=(c,n,t,p)=>lookup.get([c,n,t,p].join('|'));
const ticksN=n=>n>=1000?`${n/1000}k`:n;
const tickY=y=>y>=1000?y.toFixed(0):Number(y.toPrecision(3)).toString();
document.getElementById('chips').innerHTML=[`${D.samples} measured runs + ${D.warmups} warmups`,`CPU ${D.cpu} · ${D.cpu_model}`,`100% eligibility`,`${D.sizes.length} sizes · ${D.cases.length} workloads`].map(x=>`<span>${E(x)}</span>`).join('');
document.getElementById('legend').innerHTML=Object.keys(labels).map(t=>`<span><i class="key" style="background:${colors[t]}"></i>${E(labels[t])}</span>`).join('');
const sizeEl=document.getElementById('size');sizeEl.innerHTML=D.sizes.map(n=>`<option value="${n}">${n.toLocaleString()}</option>`).join('');sizeEl.value=D.sizes.includes(100000)?100000:D.sizes.at(-1);
function ratio(a,b){if(!a||!b||b.median===0)return '—';return (a.median/b.median).toFixed(2)+'×'+(Math.min(a.median,b.median)<.01?' †':'');}
function chart(c,p,log){
 const series=Object.keys(labels).map(t=>({t,rows:D.sizes.map(n=>get(c,n,t,p)).filter(Boolean)})).filter(s=>s.rows.length);
 const vals=series.flatMap(s=>s.rows.flatMap(r=>[r.q25,r.q75,r.median])).filter(x=>x>0);
 const min=log?Math.pow(10,Math.floor(Math.log10(Math.min(...vals)))):0;
 const max=log?Math.pow(10,Math.ceil(Math.log10(Math.max(...vals)*1.05))):Math.max(...vals)*1.12||1;
 const w=600,h=270,L=64,R=20,T=20,B=46,pw=w-L-R,ph=h-T-B;
 const xmin=Math.log10(D.sizes[0]),xmax=Math.log10(D.sizes.at(-1));
 const X=n=>L+(Math.log10(n)-xmin)/(xmax-xmin||1)*pw;
 const Y=v=>T+ph-(log?(Math.log10(Math.max(v,min))-Math.log10(min))/(Math.log10(max)-Math.log10(min)||1):v/max)*ph;
 let ticks=[];if(log){for(let k=Math.log10(min);k<=Math.log10(max)+.01;k++)ticks.push(10**k);}else for(let i=0;i<=4;i++)ticks.push(max*i/4);
 let svg=`<svg class="plot" viewBox="0 0 ${w} ${h}" role="img" aria-label="${E(c+' '+p+' timing across sizes')}"><text x="${L}" y="12" class="title">${p==='create'?'Construction':'Rewrite'} · milliseconds</text>`;
 for(const y of ticks)svg+=`<path d="M${L} ${Y(y)}H${w-R}" stroke="#29384e"/><text x="${L-9}" y="${Y(y)+4}" text-anchor="end">${tickY(y)}</text>`;
 for(const n of D.sizes)svg+=`<text x="${X(n)}" y="${h-B+20}" text-anchor="middle">${ticksN(n)}</text>`;
 svg+=`<text x="${w-R}" y="${h-4}" text-anchor="end">generator size n · log scale</text>`;
 for(const {t,rows} of series){
  svg+=`<polyline points="${rows.filter(r=>!log||r.median>0).map(r=>`${X(r.n)},${Y(r.median)}`).join(' ')}" fill="none" stroke="${colors[t]}" stroke-width="2.5"/>`;
  for(const r of rows){if(log&&r.median<=0)continue;
   const x=X(r.n),lo=Y(r.q25),hi=Y(r.q75);
   svg+=`<path d="M${x} ${lo}V${hi}M${x-4} ${lo}H${x+4}M${x-4} ${hi}H${x+4}" stroke="${colors[t]}" stroke-width="1.3"/>`;
   svg+=`<circle cx="${x}" cy="${Y(r.median)}" r="4" fill="${colors[t]}" stroke="#131e30"><title>${E(labels[t])}\nn=${r.n}\nMedian ${fmt(r.median)} ms\nIQR ${fmt(r.q25)}–${fmt(r.q75)} ms\nCV ${r.cv.toFixed(2)}% · ${r.count} runs</title></circle>`;
  }
 }
 return svg+'</svg>';
}
function cell(r){return r?`${fmt(r.median)}${r.median<.01?' †':''}<small>IQR ${fmt(r.q25)}–${fmt(r.q75)} · CV ${r.cv.toFixed(1)}%</small>`:'<span class="muted">Not supported</span>';}
function render(){
 const p=document.getElementById('phase').value,n=Number(sizeEl.value),log=document.getElementById('log').checked;
 document.getElementById('plots').innerHTML=D.cases.map(c=>{const b=get(c.id,n,'buffered',p),v=get(c.id,n,'veir',p),m=get(c.id,n,'mlir',p);return `<section class="card"><h3>${E(c.label)}</h3>${chart(c.id,p,log)}<p>At n=${n.toLocaleString()}: VeIR / buffered ${ratio(v,b)} · MLIR / buffered ${m?ratio(m,b):'not supported'}</p></section>`;}).join('');
 document.getElementById('tableTitle').textContent=`${p==='create'?'Construction':'Rewrite'} comparison · n=${n.toLocaleString()}`;
 document.getElementById('table').innerHTML=D.cases.map(c=>{const b=get(c.id,n,'buffered',p),v=get(c.id,n,'veir',p),m=get(c.id,n,'mlir',p);return `<tr><td>${E(c.label)}</td><td>${cell(b)}</td><td>${cell(v)}</td><td>${cell(m)}</td><td>${ratio(v,b)}</td><td>${ratio(m,b)}</td></tr>`;}).join('');
}
for(const id of ['phase','size','log'])document.getElementById(id).addEventListener('change',render);
document.getElementById('provenance').innerHTML=`<p>${E(D.lean_version)}<br>${E(D.lean_build)}</p><p>VeIR parent revision: <code>${E(D.veir_parent)}</code><br>Uncommitted diff SHA-256 at collection: <code>${E(D.veir_diff_sha256)}</code></p><p>MLIR checkout: <code>${E(D.mlir_checkout)}</code><br>Checkout status: ${E(D.mlir_checkout_status||'clean')}<br>MLIR CMake: <code>${E(JSON.stringify(D.mlir_build))}</code><br>MLIR compiler version: ${E(JSON.stringify(D.mlir_compiler_versions))}</p>`+Object.keys(D.binaries).map(t=>`<p><strong>${E(labels[t])}</strong><br><code>${E(D.binaries[t].path)}</code><br>SHA-256 <code>${D.binaries[t].sha256}</code></p>`).join('')+`<p><code>${E(D.machine)}</code></p>`;
document.getElementById('footer').textContent=`Collected ${D.collected_at} · ${D.rows.filter(r=>!r.warmup).length} measured process runs · ${D.rows.filter(r=>r.warmup).length} discarded warmup runs. All raw samples are embedded.`;
function download(name,text,type){const a=document.createElement('a'),u=URL.createObjectURL(new Blob([text],{type}));a.href=u;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(u),1000);}
document.getElementById('downloadJson').onclick=()=>download('buffed-vs-veir-mlir.json',JSON.stringify(D,null,2),'application/json');
document.getElementById('downloadCsv').onclick=()=>{const keys=Object.keys(D.rows[0]);const q=x=>'"'+String(x).replaceAll('"','""')+'"';download('buffed-vs-veir-mlir.csv',[keys.map(q).join(','),...D.rows.map(r=>keys.map(k=>q(r[k])).join(','))].join('\n'),'text/csv');};
render();
</script></body></html>'''


def render(data, out):
    out.mkdir(parents=True, exist_ok=True)
    embedded = json.dumps(data, separators=(",", ":")).replace("<", "\\u003c")
    text = PAGE.replace("__DATA__", embedded).replace("__COLORS__", json.dumps(COLORS)).replace("__LABELS__", json.dumps(LABELS))
    path = out / "index.html"
    path.write_text(text)
    print(f"HTML: {path.resolve()}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evaluation", type=Path, default=ROOT.parent / "buffed-evaluation")
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/buffed-vs-veir-mlir")
    parser.add_argument("--render", type=Path, help="Render existing data; do not run benchmarks")
    parser.add_argument("--sizes", type=int, nargs="+", default=[1000, 5000, 10000, 50000, 100000, 300000])
    parser.add_argument("--samples", type=int, default=9)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--cpu", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()
    if args.samples < 2 or args.warmups < 0 or min(args.sizes) <= 0 or args.sizes != sorted(set(args.sizes)):
        parser.error("Use at least two samples and increasing, unique, positive sizes")
    data = json.loads(args.render.read_text()) if args.render else collect(args)
    render(data, args.output)


if __name__ == "__main__":
    main()
