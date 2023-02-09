
We use the Github based PR workflow.

When starting to work on an issue create a branch and an according pull request that fixes the issue.

The changeset in a pull requests must not be larger than 1000 lines.

If an issue needs more work than that, split it into multiple pull requests.

Make sure that your PR follows the template below.

After submitting the pull request, verify that all [status checks](https://help.github.com/articles/about-status-checks/) are passing.

While the prerequisites above must be satisfied prior to having your pull request reviewed, the reviewer(s) may ask you to complete additional design work, tests, or other changes before your pull request can be accepted.

### PR & Commit Guidelines

- Split out mass-changes or mechanical changes into a separate PR from the substantive changes.
- Separate commits into conceptually-separate pieces for review purposes (even if you then later collapse them into a single changeset to merge), if technically possible.
- Address all comments from previous reviews (either by fixing as requested, or explaining why you haven't) before requesting another review.
- If your request only relates to part of the changes, say so clearly.

### PR Template

- Link to an open issue and assign yourself to the issue and the PR (if possible).
- It must be possible to understand the design of your change from the description. If it's not possible to get a good idea of what the code will be doing from the description here, the pull request may be closed. Keep in mind that the reviewer may not be familiar with or have worked with the code here recently, so please walk us through the concepts.
- Explain what other alternates were considered and why the proposed version was selected.
- What are the possible side-effects or negative impacts of the code change?
- What process did you follow to verify that your change has the desired effects?
- How did you verify that all new functionality works as expected?
- How did you verify that all changed functionality works as expected?
- How did you verify that the change has not introduced any regressions?
- Describe the actions you performed (including buttons you clicked, text you typed, commands you ran, etc.), and describe the results you observed.
- If this is a user-facing change please describe the changes in a single line that explains this improvement in terms that a library user can understand.

## Styleguides 🖋

### Git Commit Messages

- Use the present tense
- Use the imperative mood
- Limit the first line to 80 characters
- Reference issues and pull requests liberally after the first line
- If the patch is of nontrivial size, point to the important comments in the non-first lines of the commit message.

### Rust Styleguide

Use `rustfmt` on everything.

### Rustdoc

Use `rustdoc`. See an example [here](https://github.com/cryspen/hpke-spec)

## Reviews 👀

As a reviewer always keep in mind the following principles

- Reviewing code is more valuable than writing code as it results in
higher overall project activity. If you find you can't write code any
more due to prioritising reviews over coding, let's talk.
- You should respond to a review request within one working day of
getting it, either with a review, a deadline by which you promise to do
the review, or a polite refusal. If you think a patch is lower priority
than your other work communicate that.

### Review Guidelines

- Check that issue is assigned and linked.
- Commit title and message make sense and say what is being changed.
- Check that the PR applies cleanly on the target branch.
- Check new files for license and administrative issues.
- Check out code changes
    - Run automated tests
    - Manually verify changes if possible
- Code review
    - Does the change address the issue at hand?
    - Is the code well documented?
    - Do you understand the code changes?
        - If not, add a comment. The PR can't be accepted if you don't understand the changes.
    - Is the public API changed?
        - Are the changes well documented for consumers?
        - Do the changes break backwards compatibility?
        - Is the new API sensible/needed?
    - Is the code maintainable after the changes?
    - Could there be any security issues with the changes?
    - Are all code changes tested?
    - Do the changes affect performance?
    - Look at the interdiff for second and subsequent reviews.
- Ask if more information is needed to understand and judge the changes.
