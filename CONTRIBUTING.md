# Contributing to CERTEUS

We welcome contributions to CERTEUS! This document provides guidelines and information about contributing to the project.

## Ì¥ù How to Contribute

### Reporting Issues

1. **Bug Reports**: Use [GitHub Issues](https://github.com/CERTEUS/certeus/issues) with the "bug" label
2. **Feature Requests**: Use [GitHub Discussions](https://github.com/CERTEUS/certeus/discussions) 
3. **Security Issues**: Email [security@certeus.io](mailto:security@certeus.io)

### Development Process

1. **Fork** the repository
2. **Clone** your fork locally
3. **Create** a feature branch: `git checkout -b feature/your-feature-name`
4. **Make** your changes
5. **Test** your changes thoroughly
6. **Commit** with descriptive messages
7. **Push** to your fork
8. **Submit** a pull request

### Development Setup

```bash
# Clone your fork
git clone https://github.com/YOUR_USERNAME/certeus.git
cd certeus

# Create virtual environment
python -m venv .venv
source .venv/bin/activate  # Linux/Mac
.venv\Scripts\activate     # Windows

# Install development dependencies
pip install -r requirements.txt
pip install -r requirements-dev.txt

# Run tests
pytest

# Start development server
python -m certeus.main
```

## Ì≥ù Contribution Guidelines

### Code Style

- **Python**: Follow PEP 8, use `black` for formatting, `ruff` for linting
- **TypeScript**: Follow standard TypeScript conventions
- **Documentation**: Use clear, concise language with examples

### Commit Messages

Use conventional commit format:
```
type(scope): description

[optional body]

[optional footer]
```

Types: `feat`, `fix`, `docs`, `style`, `refactor`, `test`, `chore`

Example:
```
feat(api): add quantum measurement endpoint

Add new /api/v1/quantum/measure endpoint for QTMP protocol
with formal verification and proof generation.

Closes #123
```

### Pull Request Process

1. **Update documentation** for any new features
2. **Add tests** for new functionality
3. **Ensure CI passes** all checks
4. **Get code review** from maintainers
5. **Squash commits** before merge

### Testing Requirements

- **Unit tests**: Cover new functionality
- **Integration tests**: For API endpoints
- **End-to-end tests**: For critical workflows
- **Security tests**: For security-sensitive changes

## Ì∑™ Quality Standards

### Code Quality Gates

All contributions must pass:

- ‚úÖ **Linting**: `ruff check`
- ‚úÖ **Formatting**: `black --check`
- ‚úÖ **Type checking**: `mypy`
- ‚úÖ **Tests**: `pytest` with >90% coverage
- ‚úÖ **Security**: `bandit` security analysis

### Documentation Standards

- **API changes**: Update OpenAPI specification
- **New features**: Add documentation and examples
- **Breaking changes**: Update migration guide

## ÌøóÔ∏è Architecture Guidelines

### Code Organization

```
certeus/
‚îú‚îÄ‚îÄ core/           # Core business logic
‚îú‚îÄ‚îÄ api/            # REST API endpoints
‚îú‚îÄ‚îÄ packs/          # Domain-specific modules
‚îú‚îÄ‚îÄ utils/          # Utility functions
‚îú‚îÄ‚îÄ tests/          # Test suites
‚îî‚îÄ‚îÄ docs/           # Documentation
```

### Design Principles

1. **Proof-Only Architecture**: Every output must carry cryptographic proof
2. **Formal Verification**: Use mathematical proofs where possible
3. **Zero-Trust Security**: Verify everything, trust nothing
4. **Domain Extensibility**: Support pluggable domain packs

## Ì∫® Security Guidelines

### Security Best Practices

- **Input validation**: Validate all user inputs
- **Secrets management**: Never commit secrets to code
- **Cryptography**: Use established cryptographic libraries
- **Dependencies**: Keep dependencies updated and audited

### Security Review Process

Security-sensitive changes require:
1. **Security review** by security team
2. **Threat modeling** for new features
3. **Penetration testing** for major changes

## ÔøΩÔøΩÔ∏è Release Process

### Versioning

We use [Semantic Versioning](https://semver.org/):
- **MAJOR**: Breaking changes
- **MINOR**: New features (backward compatible)
- **PATCH**: Bug fixes (backward compatible)

### Release Checklist

- [ ] Update version numbers
- [ ] Update CHANGELOG.md
- [ ] Run full test suite
- [ ] Update documentation
- [ ] Create release notes
- [ ] Tag release in Git

## Ì≥û Getting Help

### Communication Channels

- **Technical Questions**: [GitHub Discussions](https://github.com/CERTEUS/certeus/discussions)
- **Real-time Chat**: [Discord](https://discord.gg/certeus)
- **Email**: [contributors@certeus.io](mailto:contributors@certeus.io)

### Mentorship Program

New contributors can get:
- **Code review mentorship**
- **Architecture guidance**
- **Project direction alignment**

Contact: [mentorship@certeus.io](mailto:mentorship@certeus.io)

## ÌæØ Good First Issues

Look for issues labeled:
- `good-first-issue`: Great for newcomers
- `help-wanted`: Community help needed
- `documentation`: Documentation improvements

## Ì≥ú Code of Conduct

This project follows our [Code of Conduct](CODE_OF_CONDUCT.md). Please read and follow it in all interactions.

## Ìπè Recognition

Contributors are recognized in:
- **README.md**: Core contributors section
- **Release notes**: Feature contributors
- **Documentation**: Technical writers
- **Community**: Active community members

Thank you for contributing to CERTEUS! Ì∫Ä
