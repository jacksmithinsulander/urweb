/** Click button, expect alert "AHOY" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Button/main');
  let dialogMsg = null;
  page.once('dialog', async dialog => {
    dialogMsg = dialog.message();
    await dialog.accept();
  });
  await page.click('xpath=/html/body/button');
  if (dialogMsg !== 'AHOY') {
    throw new Error(`Expected alert "AHOY", got: ${dialogMsg}`);
  }
};
