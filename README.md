# syn bat obfuscator

## how to use

interactive / drag-and-drop:
- run `obfuscator.exe` and drag a `.bat` file into the window, or drop a `.bat` file onto `obfuscator.exe`

cli:

```bash
obfuscator.exe input.bat -o output.bat [flags]
```

## flags

- `-o`, `--output <path>`: output `.bat` / `.cmd` file
- `--vm-level <0-3>`: vm virtualization level (default `3`)
- `--layers <1-5>`: recursive obfuscation layers (default `2`)
- `--junk <0-10>`: junk variables and dead code amount (default `5`)
- `--seed <uint32>`: deterministic rng seed (random if omitted)
- `--zalgo`: inject zalgo noise comments (default `off`)
- `--no-flatten`: disable control flow flattening (default `enabled`)
- `--no-anti-tamper`: disable file-size integrity check (default `enabled`)
