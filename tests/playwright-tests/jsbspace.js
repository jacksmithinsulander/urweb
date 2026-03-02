/** Click button, alert "Some \btext" (literal backslash-b, not backspace) */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Jsbspace/main');
  let dialogMsg = null;
  page.once('dialog', async dialog => {
    dialogMsg = dialog.message();
    await dialog.accept();
  });
  await page.click('xpath=/html/body/button');
  if (dialogMsg !== 'Some \\btext') {
    throw new Error(`Expected alert "Some \\\\btext", got: ${JSON.stringify(dialogMsg)}`);
  }
};
