/** Click body -> alert "You clicked the body."; send 'h' -> alert "Key" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/BodyClick/main');
  const body = page.locator('body');

  let dialogMsg1 = null;
  page.once('dialog', async dialog => {
    dialogMsg1 = dialog.message();
    await dialog.accept();
  });
  await body.click();
  if (dialogMsg1 !== 'You clicked the body.') {
    throw new Error(`Expected "You clicked the body.", got: ${dialogMsg1}`);
  }

  let dialogMsg2 = null;
  page.once('dialog', async dialog => {
    dialogMsg2 = dialog.message();
    await dialog.accept();
  });
  await body.press('h');
  if (dialogMsg2 !== 'Key') {
    throw new Error(`Expected "Key", got: ${dialogMsg2}`);
  }
};
