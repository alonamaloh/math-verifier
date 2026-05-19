# VS Code integration

Two files in `.vscode/` give you build-on-save + clickable errors in the
Problems panel + hover-style error context.

## `.vscode/tasks.json`

```json
{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "math: build library",
      "type": "shell",
      "command": "make",
      "args": ["-j", "16", "library"],
      "group": { "kind": "build", "isDefault": true },
      "presentation": {
        "echo": true,
        "reveal": "silent",
        "focus": false,
        "panel": "shared",
        "showReuseMessage": false,
        "clear": true
      },
      "problemMatcher": {
        "owner": "math",
        "fileLocation": ["relative", "${workspaceFolder}"],
        "pattern": [
          {
            "regexp": "^(.+\\.math):(\\d+):(\\d+):\\s+(parse|elaborate|type|lex)\\s+error:\\s+(.*)$",
            "file": 1, "line": 2, "column": 3,
            "severity": 4, "message": 5
          }
        ]
      }
    },
    {
      "label": "math: build library (watch)",
      "type": "shell",
      "command": "fswatch",
      "args": ["-or", "library/", "axioms.math", "|",
               "xargs", "-n1", "-I{}", "make", "-j", "16", "library"],
      "isBackground": true,
      "presentation": {
        "reveal": "silent", "panel": "dedicated", "clear": false
      },
      "problemMatcher": {
        "owner": "math",
        "fileLocation": ["relative", "${workspaceFolder}"],
        "background": {
          "activeOnStart": true,
          "beginsPattern": "^.+\\.math$",
          "endsPattern": "^(verified|.+: (parse|elaborate|type|lex) error:).*$"
        },
        "pattern": [
          {
            "regexp": "^(.+\\.math):(\\d+):(\\d+):\\s+(parse|elaborate|type|lex)\\s+error:\\s+(.*)$",
            "file": 1, "line": 2, "column": 3,
            "severity": 4, "message": 5
          }
        ]
      }
    }
  ]
}
```

The first task runs once on `Cmd+Shift+B` (the default build keystroke).
The second is a background watch — pick "Tasks: Run Task" → "math: build
library (watch)" and leave it running for the session.

## Errors in the Problems panel

Both tasks register their problem matcher with the `math` owner. After a
build, Problems shows entries like

```
library/Real/basics.math    96:1   elaborate error: ring at line 96
    context:
      a : Rational
      ...
    goal: ...
```

Clicking jumps to the offending line. The multi-line breadcrumb shows
up in the message; for now it lives in the Problems panel — VS Code
doesn't (yet) render it inline in the editor. That's the polish step
the LSP daemon (Shape C) would add.

## Optional: keystroke for "rebuild now"

Add to `keybindings.json`:

```json
{
  "key": "cmd+r",
  "command": "workbench.action.tasks.runTask",
  "args": "math: build library",
  "when": "editorTextFocus && resourceExtname == .math"
}
```

Now `Cmd+R` in any `.math` file kicks off a build.

## Caveat: `fswatch` path

Some Homebrew installs put `fswatch` outside the default VS Code
terminal `PATH`. If the watch task can't find it, add
`/opt/homebrew/bin` (Apple Silicon) or `/usr/local/bin` (Intel) to your
shell's PATH and restart the VS Code window, or replace `fswatch` in
`tasks.json` with the absolute path.
