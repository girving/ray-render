Formalised Mandelbrot renders
=============================

[![build](https://github.com/girving/ray-render/actions/workflows/lean.yml/badge.svg)](https://github.com/girving/ray-render/actions/workflows/lean.yml)

We build on [verified interval arithmetic](https://github.com/girving/interval) and
[verified holomorphic dynamics results](https://github.com/girving/ray) for verified
rendering of the Mandelbrot set and its potential function. For now, all we have is
potential function renders such as

<p align="center">
  <img src="gallery/potential-2024feb9.png" width="1024" height="951" title="Mandelbrot potential function">
</p>

The semantics of this render are that the color of each pixel is off by at most
one in each coordinate, except for red pixels which can have arbitrary error.
And there are only a few of those!

## Building

1. Install [`elan`](https://github.com/leanprover/elan) (`brew install elan-init` on Mac)
2. `lake build`

## Optimization and debugging tricks

I'm going to keep a list here, since otherwise I will forget them.

```
-- Tracing options
set_option trace.aesop true in

-- Print compiler IR, such as to see how well inlining worked:
set_option trace.compiler.ir.result true in
def ...
```
