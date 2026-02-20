/** Click body -> alert "You clicked the body."; send 'h' -> alert "Key" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/BodyClick/main');
  const body = page.locator('body');

  const d1 = page.waitForEvent('dialog');
  await body.click();
  const dialog1 = await d1;
  if (dialog1.message() !== 'You clicked the body.') {
    throw new Error(`Expected "You clicked the body.", got: ${dialog1.message()}`);
  }
  await dialog1.accept();

  const d2 = page.waitForEvent('dialog');
  await body.press('h');
  const dialog2 = await d2;
  if (dialog2.message() !== 'Key') {
    throw new Error(`Expected "Key", got: ${dialog2.message()}`);
  }
  await dialog2.accept();
};
