# Development

Clone the repo. Make a new virtualenv and activate it. Then from the repo root, run:

```
pip install -e .
```

This will install the package such that any changes you make to the source are respected.

## Testing

Tests (located under `test/`) assume that you have run the above command. Test scripts should run without throwing an error.

TODO: Add negative test cases that the prover is expected to reject. Current set of tests is incomplete in this regard.

# Release

## Checklist

* Have you tested your changes thoroughly, including with the test script(s)?
* Have you incremented the version number?
* Have the changes been committed to the repo?

Then it's time to publish to PyPI!

## Steps

In your virtualenv, make sure you have installed the `build` and `twine` packages. (`pip install -U build twine`)

```
python -m build
python -m twine check dist/*
python -m twine upload --repository pypi dist/*
```

Paste your pypi token.

