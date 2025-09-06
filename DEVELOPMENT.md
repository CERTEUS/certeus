# CERTEUS Development Environment Setup

This document describes the standardized development environment setup for CERTEUS project.

## Prerequisites

- Python 3.11+
- Git
- VS Code (recommended)

## Quick Setup

1. **Clone the repository:**
   ```bash
   git clone https://github.com/CERTEUS/certeus.git
   cd certeus
   ```

2. **Create virtual environment:**
   ```bash
   python -m venv .venv
   source .venv/bin/activate  # Linux/Mac
   # or
   .venv\Scripts\activate     # Windows
   ```

3. **Install dependencies:**
   ```bash
   pip install -r requirements.txt
   ```

4. **Open in VS Code:**
   ```bash
   code .
   ```

## Environment Configuration

The project includes standardized configuration files:

### VS Code Configuration
- `.vscode/settings.json` - Editor settings, Python configuration
- `.vscode/extensions.json` - Recommended extensions
- `.vscode/tasks.json` - Common tasks (test, lint, format)
- `.vscode/launch.json` - Debug configurations

### Python Configuration
- `pyrightconfig.json` - Pylance/Pyright type checker settings
- `.pylanceignore` - Files to ignore in Python analysis
- `.editorconfig` - Cross-editor formatting rules

### Key Features
- **Pylance optimization**: Configured for performance with large codebases
- **Virtual environment isolation**: `.venv` directories are excluded from analysis
- **Cross-platform compatibility**: Consistent line endings, encoding
- **Performance tuning**: File watchers and search exclusions

## Recommended Extensions

The project automatically suggests these VS Code extensions:
- Python language support (ms-python.python)
- Pylance (ms-python.vscode-pylance)
- Black formatter (ms-python.black-formatter)
- GitHub Copilot (github.copilot)
- EditorConfig (editorconfig.editorconfig)
- YAML support (redhat.vscode-yaml)

## Common Tasks

Use VS Code Command Palette (Ctrl+Shift+P):
- `Tasks: Run Task` → `Python: Run Tests`
- `Tasks: Run Task` → `Python: Format Code`
- `Tasks: Run Task` → `Python: Lint Code`

## Troubleshooting

### Pylance Issues
If you see too many Python errors from virtual environment:
1. Ensure `.venv` is excluded in settings
2. Check `python.analysis.diagnosticMode` is set to `"openFilesOnly"`
3. Restart Pylance: Command Palette → `Python: Restart Language Server`

### Performance Issues
If VS Code is slow:
1. Check file exclusions in `.vscode/settings.json`
2. Ensure `python.analysis.indexing` is `false`
3. Verify `.pylanceignore` patterns are working

## Environment Variables

Create `.env` file in project root for local configuration:
```env
PYTHONPATH=.
CERTEUS_ENV=development
```

## Testing

Run tests with:
```bash
python -m pytest tests/ -v
```

Or use VS Code task: `Python: Run Tests`
