"""Command line: ``python3 -m numerics [check ...] [--jobs N] [--out FILE] [--quick]``.

Checks: ``selftest``, ``remark``, ``dout``, ``subclaims``, ``celltwo``, ``unstable`` (placeholder),
``all`` (the default). Results are printed and written as JSON to ``--out``
(default ``notes/ref/results.json`` relative to the repository root).
"""
import argparse
import json
import os
import time


def main(argv=None):
    ap = argparse.ArgumentParser(prog='python3 -m numerics')
    ap.add_argument('checks', nargs='*', default=['all'])
    ap.add_argument('--jobs', type=int, default=None, help='worker processes (default min(10, cpus))')
    ap.add_argument('--out', default=None)
    ap.add_argument('--quick', action='store_true', help='skip the certified-margin runs')
    a = ap.parse_args(argv)
    if a.jobs is not None:
        os.environ['NUMERICS_JOBS'] = str(a.jobs)
    from . import report
    names = a.checks
    if 'all' in names:
        names = ['selftest', 'remark', 'dout', 'subclaims', 'celltwo', 'unstable']
    res = {}
    t0 = time.time()
    for n in names:
        t1 = time.time()
        print('== %s' % n, flush=True)
        r = report.RUNNERS[n](quick=a.quick)
        r['wall_time_s'] = round(time.time() - t1, 1)
        res[n] = r
        print(json.dumps(r, indent=1, default=str)[:6000], flush=True)
    res['total_wall_time_s'] = round(time.time() - t0, 1)
    out = a.out or os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                                'notes', 'ref', 'results.json')
    try:
        old = json.load(open(out))
    except (OSError, ValueError):
        old = {}
    old.update(res)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w') as f:
        json.dump(old, f, indent=1, default=str)
    print('written', out)


if __name__ == '__main__':
    main()
