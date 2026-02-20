/** Click button, expect alert "AHOY" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Button/main');
  const dialogPromise = page.waitForEvent('dialog');
  await page.click('xpath=/html/body/button');
  const dialog = await dialogPromise;
  if (dialog.message() !== 'AHOY') {
    throw new Error(`Expected alert "AHOY", got: ${dialog.message()}`);
  }
  await dialog.accept();
};
