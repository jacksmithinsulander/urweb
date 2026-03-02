/** Click Register, click Send, alert "Got something from the channel", body has "blabla" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/DynChannel/main');
  // Click Register (first/only button initially)
  await page.click('xpath=/html/body/button');
  // Wait for Send button to appear in body (rendered by dyn after RPC)
  await page.waitForSelector('button:has-text("Send")');
  // Set up dialog handler before clicking Send
  let dialogMsg = null;
  page.once('dialog', async dialog => {
    dialogMsg = dialog.message();
    await dialog.accept();
  });
  await page.getByRole('button', { name: 'Send' }).click();
  // Wait for channel message to arrive and dyn to render "blabla"
  await page.waitForFunction(() => document.body.textContent.includes('blabla'), { timeout: 15000 });
  if (dialogMsg !== 'Got something from the channel') {
    throw new Error(`Expected "Got something from the channel", got: ${dialogMsg}`);
  }
  const bodyText = await page.evaluate(() => document.body.textContent);
  if (!bodyText.includes('blabla')) {
    throw new Error(`Expected "blabla" in page body, got: ${bodyText}`);
  }
};
