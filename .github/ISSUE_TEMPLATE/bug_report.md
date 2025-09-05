name: Bug report
labels: [bug]
assignees: []
body:

- type: textarea
  id: summary
  attributes:
  label: Summary
  description: Short description of the bug
  validations:
  required: true
- type: textarea
  id: steps
  attributes:
  label: Steps to reproduce
  description: Provide steps, logs, and environment info
  validations:
  required: true
- type: textarea
  id: expected
  attributes:
  label: Expected behavior
  validations:
  required: true
