This file contains instructions to setup Claude Code with Lean MCP tools in
order to maximize its accuracy and your productivity.

For commands past 1. you should run them at the root of the `sp1-lean` repo.

1. Install [uv](https://docs.astral.sh/uv/).

2. Run `uvx --from lean-explore leanexplore data fetch` to download a database
   about mathlib4. You can still get a (free) API key from
   [LeanExplore](https://www.leanexplore.com/docs/mcp) but in practice I've
   found that it's too easy to hit API limits.

   This downloads around 6GB of files so it may take some time.

3. Run `claude mcp add -s local LeanExplore -- uvx --from lean-explore
   leanexplore mcp serve --backend local` to add LeanExplore as a MCP sever.

4. Run `claude mcp add -s local lean-lsp -- uvx lean-lsp-mcp` to add the Lean
   LSP as a MCP server.

5. Run `claude mcp list` and make sure both servers are shown as "connected".
   The first run may take some time.

6. These tools are auto-discoverable by Lean. If they're not picking it up, you
   can tell Claude to use them explicitly by saying things like "use the tool to
   do X". See [Example
   Uses](https://github.com/oOo0oOo/lean-lsp-mcp?tab=readme-ov-file#example-uses)
   section from lean-lsp-mcp for more examples.

Occasionally the tool may hover in the middle or after a `sorry`, causing it not
being able to get the context and goal. When this happens, just tell it to
"hover at the 's' of sorry to see the context and goal at the `sorry`".

Remember to run `lake build` or `lake lean <the-file-to-work-on>` for the Lean
LSP MCP server to work, including when you see the message like
"X has been changed,
please reopen/rebuild" in VSCode. In other words, this MCP
server doesn't support the usecase where you
change a dependency of a file and pretend nothing has been changed by not
closing/reopening the file.
Note that the build doesn't have to succeed. For more info see [its
docs](https://github.com/oOo0oOo/lean-lsp-mcp?tab=readme-ov-file#2-run-lake-build).

