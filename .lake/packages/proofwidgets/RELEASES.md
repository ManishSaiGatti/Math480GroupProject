# ProofWidgets4 releases

This file contains work-in-progress notes for the upcoming release, as well as previous releases.
Please check the [releases](https://github.com/leanprover-community/ProofWidgets4/releases) page for the build artifacts.

v0.0.49 (WIP)
-------------
* Published [@leanprover-community/proofwidgets4](https://www.npmjs.com/package/@leanprover-community/proofwidgets4) on NPM.
  This allows importing ProofWidgets4 JS components from widgets defined in other Lean packages.
  NPM support is experimental: see [discussion](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/ProofWidgets.2EHtml.20to.20JSX.2EElement/near/488669256).

v0.0.47
-------
* Generalized `GraphDisplay.Vertex.radius` to `GraphDisplay.Vertex.boundingShape`.
* Added demo of metavariable graph display in tactic proofs.

v0.0.46
-------

* Renamed `DigraphDisplay` to `GraphDisplay`.
  Undirected graphs can be rendered by turning off arrowheads.
* Added support for edge labels and more customization to `GraphDisplay`.

v0.0.45
-------

* Updated Lean to v4.14.0-rc1.

v0.0.44
-------

* Added `DigraphDisplay` component. It uses [d3-force](https://d3js.org/d3-force) for layout
  and can accommodate a variety of display styles.
  See `Demos/Digraph.lean` for more.
* Added `MarkdownDisplay` component to display Markdown (including LaTeX).
* Fixed cloud release issue (see [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/cache.20and.20proofwidgets)).

v0.0.30
-------

* Moved the toolchain to `leanprover/lean4:v4.7.0-rc1`.
* Performance improvements for widgets using `mk_rpc_widget%`. Redundant, duplicate calls were previously made to the underlying RPC method; this has been fixed. Furthermore, serverside execution of the RPC method gets cancelled by the infoview as long as its results are no longer needed (for example because the user moved the cursor elsewhere). To opt into this mechanism, use `@[server_rpc_method_cancellable]` instead of `@[server_rpc_method]`. RPC methods using that attribute can check whether they have been cancelled using [IO.checkCanceled](https://leanprover-community.github.io/mathlib4_docs/Init/System/IO.html#IO.checkCanceled), and immediately return with an error or a partial result.

v0.0.29
-------

* Moved the toolchain to `leanprover/lean4:v4.6.0`.
* Exposed `theme.background` to Penrose style programs.

v0.0.26 - v0.0.28
-------

* Toolchain bumps and associated tweaks.

v0.0.25
-------

* Build the demos in CI.

v0.0.24
-------

* Moved the toolchain to `leanprover/lean4:v4.5.0-rc1`.
  This brings changes to the user widget API described [here](https://github.com/leanprover/lean4/blob/master/RELEASES.md#v450).
* **Removed** `ProofWidgets.savePanelWidgetInfo`. For now you should use `Lean.Widget.savePanelWidgetInfo` instead.
  An example migration can be found [here](https://github.com/leanprover-community/ProofWidgets4/compare/v0.0.23..v0.0.24#diff-c48bcbf1b4d226947726f7a0fe8c945f082f4195b34681638ca61a776bbf778eL49-R52).
* The `with_panel_widgets` tactic now optionally accepts props for each listed widget.
* Several components now use `mk_rpc_widget%` instead of JavaScript string literals.
* Fixes and improvements in the `PenroseDiagram` component and the `Euclidean` demo.
