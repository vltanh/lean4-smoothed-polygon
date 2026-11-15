"""Adaptive subdivision with statistics, in parallel over the root boxes.

``run(roots, leaf, ...)`` proves a property of every box in ``roots``: ``leaf(box)`` returns
``(True, margin, info)`` when it certifies the box (``margin`` a rigorous lower bound of the margin
of the property on the box), or ``(False, axis, info)`` to ask for a split (``axis`` the coordinate
to halve, or ``None`` for the default: the widest coordinate, ``r2`` weighted by ``W_R``), or
``(False, [boxes], info)`` to replace the box by boxes that cover it (the blow-up charts). A box
that still fails at depth ``max_depth``, or is still open when its root has run for ``time_limit``
seconds, is recorded as a failure; the run proves the property iff there are no failures. The statistics: the number of certified leaves, of evaluated boxes, the maximal
depth, the smallest certified margin and the box where it is attained, the time.
"""
import os
import time
import multiprocessing as mp

W_R = 2.0


def default_axis(b):
    w = b.widths()
    ws = (w[0] * W_R, w[1], w[2])
    return max(range(3), key=lambda k: ws[k])


class Stats:
    def __init__(self):
        self.leaves = 0
        self.evals = 0
        self.depth = 0
        self.min_margin = float('inf')
        self.min_box = None
        self.min_info = None
        self.failures = []
        self.time = 0.0
        self.kinds = {}

    def merge(self, o):
        self.leaves += o.leaves
        self.evals += o.evals
        self.depth = max(self.depth, o.depth)
        if o.min_margin < self.min_margin:
            self.min_margin, self.min_box, self.min_info = o.min_margin, o.min_box, o.min_info
        self.failures.extend(o.failures)
        for k, v in o.kinds.items():
            self.kinds[k] = self.kinds.get(k, 0) + v

    def ok(self):
        return not self.failures

    def summary(self):
        return dict(proved=self.ok(), leaves=self.leaves, evals=self.evals, depth=self.depth,
                    min_margin=self.min_margin, min_box=repr(self.min_box),
                    min_info=self.min_info, failures=[repr(f) for f in self.failures[:10]],
                    n_failures=len(self.failures), time=round(self.time, 2), kinds=self.kinds)


def _prove(root, leaf, max_depth, max_fail, time_limit=None):
    st = Stats()
    stack = [(root, 0)]
    t0 = time.time()
    while stack:
        if time_limit is not None and time.time() - t0 > time_limit:
            # out of time: the open boxes are recorded as not proved
            for b, d in stack:
                st.failures.append((b, {'why': 'time limit'}))
            break
        b, d = stack.pop()
        st.evals += 1
        st.depth = max(st.depth, d)
        ok, val, info = leaf(b)
        if ok:
            st.leaves += 1
            k = info.get('kind', '') if isinstance(info, dict) else ''
            st.kinds[k] = st.kinds.get(k, 0) + 1
            if val < st.min_margin:
                st.min_margin, st.min_box, st.min_info = val, b, info
            continue
        if d >= max_depth:
            st.failures.append((b, info))
            if len(st.failures) >= max_fail:
                break
            continue
        if isinstance(val, list):
            # the leaf replaces the box by a cover (e.g. the blow-up charts of an edge)
            for c in val:
                stack.append((c, d + 1))
            continue
        axis = val if val is not None else default_axis(b)
        b1, b2 = b.split(axis)
        stack.append((b2, d + 1))
        stack.append((b1, d + 1))
    return st


_G = {}


def _worker(args):
    i = args
    root = _G['roots'][i]
    return _prove(root, _G['leaf'], _G['max_depth'], _G['max_fail'], _G.get('time_limit'))


def run(roots, leaf, max_depth=40, max_fail=20, jobs=None, presplit=0, time_limit=None):
    """prove leaf on every box of roots; presplit: halve each root this many times first (to feed
    the worker processes)"""
    t0 = time.time()
    rs = list(roots)
    for _ in range(presplit):
        nxt = []
        for b in rs:
            nxt.extend(b.split(default_axis(b)))
        rs = nxt
    jobs = jobs if jobs is not None else int(os.environ.get("NUMERICS_JOBS", min(10, os.cpu_count() or 1)))
    st = Stats()
    if jobs <= 1 or len(rs) == 1:
        for r in rs:
            st.merge(_prove(r, leaf, max_depth, max_fail, time_limit))
    else:
        _G.update(roots=rs, leaf=leaf, max_depth=max_depth, max_fail=max_fail,
                  time_limit=time_limit)
        ctx = mp.get_context('fork')
        prog = os.environ.get('NUMERICS_PROGRESS')
        with ctx.Pool(jobs) as pool:
            cs = max(1, len(rs) // (jobs * 4))   # neighbouring roots to one worker (its caches)
            for k, s in enumerate(pool.imap_unordered(_worker, range(len(rs)), chunksize=cs)):
                st.merge(s)
                if prog and (k + 1) % max(1, len(rs) // 20) == 0:
                    import sys
                    print('  [%d/%d roots] leaves %d, evals %d, failures %d, %.0f s' % (
                        k + 1, len(rs), st.leaves, st.evals, len(st.failures), time.time() - t0),
                        file=sys.stderr, flush=True)
    st.time = time.time() - t0
    return st
